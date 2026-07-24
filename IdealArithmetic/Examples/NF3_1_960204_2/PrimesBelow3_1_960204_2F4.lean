
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 24, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-29, 24, 0]] 
 ![![197, 0, 0], ![7, 1, 0], ![117, 0, 1]] where
  M :=![![![-29, 24, 0], ![-24, -53, 72], ![1224, -1008, -5]]]
  hmulB := by decide  
  f := ![![![-72841, -120, -1728]], ![![-3035, -5, -72]], ![![-43713, -72, -1037]]]
  g := ![![![-1, 24, 0], ![-41, -53, 72], ![45, -1008, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![71, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![71, 1, 0]] 
 ![![197, 0, 0], ![71, 1, 0], ![116, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![71, 1, 0], ![-1, 70, 3], ![51, -42, 72]]]
  hmulB := by decide  
  f := ![![![-17759, 1243200, 53280], ![0, -3498720, 0]], ![![-6400, 448000, 19200], ![1, -1260800, 0]], ![![-10496, 732036, 31373], ![108, -2060160, 0]]]
  g := ![![![1, 0, 0], ![-71, 197, 0], ![-116, 0, 197]], ![![0, 1, 0], ![-27, 70, 3], ![-27, -42, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-78, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-78, 1, 0]] 
 ![![197, 0, 0], ![119, 1, 0], ![47, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-78, 1, 0], ![-1, -79, 3], ![51, -42, -77]]]
  hmulB := by decide  
  f := ![![![-11323, -894596, 33972], ![0, -2230828, 0]], ![![-6839, -540360, 20520], ![1, -1347480, 0]], ![![-2665, -213432, 8105], ![92, -532228, 0]]]
  g := ![![![1, 0, 0], ![-119, 197, 0], ![-47, 0, 197]], ![![-1, 1, 0], ![47, -79, 3], ![44, -42, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-29, 24, 0]] ![![197, 0, 0], ![71, 1, 0]]
  ![![197, 0, 0], ![34, -40, 1]] where
 M := ![![![-5713, 4728, 0], ![-2083, 1651, 72]]]
 hmul := by decide  
 g := ![![![![-29, 24, 0], ![0, 0, 0]], ![![-23, 23, 0], ![72, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![34, -40, 1]] ![![197, 0, 0], ![-78, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-15366, 197, 0]], ![![6698, -7880, 197], ![-2561, 3152, -197]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-78, 1, 0]]], ![![![34, -40, 1]], ![![-13, 16, -1]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![46, -83, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![46, -83, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![46, 116, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![46, -83, 1], ![134, 87, -248], ![-4185, 3489, -78]]]
  hmulB := by decide  
  f := ![![![-45, 83, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -116, 199]], ![![0, -1, 1], ![58, 145, -248], ![-3, 63, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [3, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 198], [0, 1]]
 g := ![![[127, 31], [36, 117], [187, 165], [9], [1], [7], [17, 1]], ![[57, 168], [35, 82], [7, 34], [9], [1], [7], [34, 198]]]
 h' := ![![[17, 198], [91, 164], [36, 147], [99, 31], [46, 3], [192, 1], [148, 87], [0, 1]], ![[0, 1], [93, 35], [147, 52], [29, 168], [97, 196], [10, 198], [35, 112], [17, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [64, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [3, 182, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![618, 27, -921]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![216, 537, -921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![49, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![49, 1, 0]] 
 ![![199, 0, 0], ![49, 1, 0], ![78, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![49, 1, 0], ![-1, 48, 3], ![51, -42, 50]]]
  hmulB := by decide  
  f := ![![![-7669, 368160, 23010], ![0, -1526330, 0]], ![![-1888, 90624, 5664], ![1, -375712, 0]], ![![-3051, 144303, 9019], ![183, -598260, 0]]]
  g := ![![![1, 0, 0], ![-49, 199, 0], ![-78, 0, 199]], ![![0, 1, 0], ![-13, 48, 3], ![-9, -42, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![46, -83, 1]] ![![199, 0, 0], ![49, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![9751, 199, 0]], ![![9154, -16517, 199], ![2388, -3980, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![49, 1, 0]]], ![![![46, -83, 1]], ![![12, -20, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-71, 89, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-71, 89, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![140, 89, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-71, 89, 1], ![-38, -202, 268], ![4587, -3735, -23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -89, 211]], ![![-1, 0, 1], ![-178, -114, 268], ![37, -8, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [89, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 210], [0, 1]]
 g := ![![[7, 25], [36, 36], [76], [46], [54, 169], [121], [10, 1]], ![[46, 186], [185, 175], [76], [46], [56, 42], [121], [20, 210]]]
 h' := ![![[10, 210], [172, 206], [184, 6], [14, 169], [47, 62], [209, 198], [165, 11], [0, 1]], ![[0, 1], [122, 5], [33, 205], [16, 42], [34, 149], [79, 13], [64, 200], [10, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [117, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [89, 201, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1538, 2552, -1069]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![702, 463, -1069]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-57, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-57, 1, 0]] 
 ![![211, 0, 0], ![154, 1, 0], ![23, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-57, 1, 0], ![-1, -58, 3], ![51, -42, -56]]]
  hmulB := by decide  
  f := ![![![7495, 431345, -22311], ![211, 1569207, 0]], ![![5485, 314765, -16281], ![212, 1145097, 0]], ![![854, 47018, -2432], ![160, 171051, 0]]]
  g := ![![![1, 0, 0], ![-154, 211, 0], ![-23, 0, 211]], ![![-1, 1, 0], ![42, -58, 3], ![37, -42, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-71, 89, 1]] ![![211, 0, 0], ![-57, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-12027, 211, 0]], ![![-14981, 18779, 211], ![4009, -5275, 211]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-57, 1, 0]]], ![![![-71, 89, 1]], ![![19, -25, 1]]]]
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [207, 115, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [138, 150, 44], [74, 72, 179], [0, 1]]
 g := ![![[148, 53, 76], [20, 167, 121], [45, 150, 4], [118, 151, 139], [60, 152, 120], [84, 121], [1]], ![[44, 92, 125, 92], [45, 51, 206, 173], [63, 178, 191, 134], [26, 149, 137, 187], [83, 42, 206, 187], [206, 17], [113, 118, 184, 221]], ![[193, 123, 170, 63], [128, 5, 153, 83], [156, 74, 96, 162], [61, 143, 115, 62], [88, 182, 179, 143], [7, 211], [12, 67, 29, 2]]]
 h' := ![![[138, 150, 44], [97, 74, 116], [51, 13, 212], [104, 160, 2], [68, 175, 94], [39, 192, 41], [16, 108, 212], [0, 1]], ![[74, 72, 179], [127, 18, 12], [123, 198, 3], [116, 194, 48], [111, 68, 196], [71, 157, 27], [41, 176, 169], [138, 150, 44]], ![[0, 1], [212, 131, 95], [143, 12, 8], [121, 92, 173], [119, 203, 156], [116, 97, 155], [2, 162, 65], [74, 72, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 17], []]
 b := ![[], [162, 58, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [207, 115, 11, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![492237043, 122786699, -524272554]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2207341, 550613, -2350998]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![44, 12, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![44, 12, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![44, 12, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![44, 12, 1], ![39, -10, 37], ![660, -501, 15]]]
  hmulB := by decide  
  f := ![![![-43, -12, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -12, 227]], ![![0, 0, 1], ![-7, -2, 37], ![0, -3, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [196, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [188, 226], [0, 1]]
 g := ![![[50, 205], [191, 34], [23], [144], [159], [209, 7], [188, 1]], ![[0, 22], [0, 193], [23], [144], [159], [163, 220], [149, 226]]]
 h' := ![![[188, 226], [19, 146], [171, 179], [65, 134], [82, 215], [123, 39], [153, 190], [0, 1]], ![[0, 1], [0, 81], [0, 48], [60, 93], [96, 12], [191, 188], [7, 37], [188, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [52, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [196, 39, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![114, 3044, -3000]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![582, 172, -3000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-37, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-37, 1, 0]] 
 ![![227, 0, 0], ![190, 1, 0], ![212, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-37, 1, 0], ![-1, -38, 3], ![51, -42, -36]]]
  hmulB := by decide  
  f := ![![![-18951, -720176, 56856], ![0, -4302104, 0]], ![![-15861, -602756, 47586], ![1, -3600674, 0]], ![![-17709, -672587, 53099], ![-63, -4017824, 0]]]
  g := ![![![1, 0, 0], ![-190, 227, 0], ![-212, 0, 227]], ![![-1, 1, 0], ![29, -38, 3], ![69, -42, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![44, 12, 1]] ![![227, 0, 0], ![-37, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-8399, 227, 0]], ![![9988, 2724, 227], ![-1589, -454, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-37, 1, 0]]], ![![![44, 12, 1]], ![![-7, -2, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-55, 58, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-55, 58, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![174, 58, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-55, 58, 1], ![-7, -155, 175], ![3006, -2433, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-174, -58, 229]], ![![-1, 0, 1], ![-133, -45, 175], ![42, -1, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [14, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [137, 228], [0, 1]]
 g := ![![[72, 180], [99], [157, 82], [174], [173], [172, 71], [137, 1]], ![[0, 49], [99], [170, 147], [174], [173], [52, 158], [45, 228]]]
 h' := ![![[137, 228], [208, 62], [92, 127], [39, 178], [52, 116], [111, 196], [143, 206], [0, 1]], ![[0, 1], [0, 167], [87, 102], [151, 51], [143, 113], [170, 33], [198, 23], [137, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [167, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [14, 92, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![539, 27, -651]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![497, 165, -651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![54, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![54, 1, 0]] 
 ![![229, 0, 0], ![54, 1, 0], ![38, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![54, 1, 0], ![-1, 53, 3], ![51, -42, 55]]]
  hmulB := by decide  
  f := ![![![-13283, 704052, 39852], ![0, -3042036, 0]], ![![-3132, 165996, 9396], ![1, -717228, 0]], ![![-2236, 116829, 6613], ![135, -504792, 0]]]
  g := ![![![1, 0, 0], ![-54, 229, 0], ![-38, 0, 229]], ![![0, 1, 0], ![-13, 53, 3], ![1, -42, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-55, 58, 1]] ![![229, 0, 0], ![54, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![12366, 229, 0]], ![![-12595, 13282, 229], ![-2977, 2977, 229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![54, 1, 0]]], ![![![-55, 58, 1]], ![![-13, 13, 1]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![82, 81, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![82, 81, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![82, 81, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![82, 81, 1], ![-30, -41, 244], ![4179, -3399, 122]]]
  hmulB := by decide  
  f := ![![![-81, -81, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -81, 233]], ![![0, 0, 1], ![-86, -85, 244], ![-25, -57, 122]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [210, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [145, 232], [0, 1]]
 g := ![![[138, 81], [58], [171], [42, 135], [217], [13, 26], [145, 1]], ![[0, 152], [58], [171], [45, 98], [217], [55, 207], [57, 232]]]
 h' := ![![[145, 232], [140, 224], [196, 161], [34, 138], [27, 169], [66, 123], [73, 78], [0, 1]], ![[0, 1], [0, 9], [8, 72], [6, 95], [67, 64], [193, 110], [199, 155], [145, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [169, 168]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [210, 88, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7911, -4776, 804]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-249, -300, 804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-11, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-11, 1, 0]] 
 ![![233, 0, 0], ![222, 1, 0], ![111, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-11, 1, 0], ![-1, -12, 3], ![51, -42, -10]]]
  hmulB := by decide  
  f := ![![![-9778, -117348, 29337], ![0, -2278507, 0]], ![![-9316, -111804, 27951], ![1, -2170861, 0]], ![![-4658, -55904, 13976], ![4, -1085469, 0]]]
  g := ![![![1, 0, 0], ![-222, 233, 0], ![-111, 0, 233]], ![![-1, 1, 0], ![10, -12, 3], ![45, -42, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![82, 81, 1]] ![![233, 0, 0], ![-11, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-2563, 233, 0]], ![![19106, 18873, 233], ![-932, -932, 233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-11, 1, 0]]], ![![![82, 81, 1]], ![![-4, -4, 1]]]]
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [203, 186, 143, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 62, 70], [0, 176, 169], [0, 1]]
 g := ![![[162, 209, 3], [12, 191, 198], [68, 47, 11], [36, 77, 170], [215, 155], [227, 96, 134], [1]], ![[146, 58, 121, 95], [125, 87, 237, 195], [223, 66, 114, 231], [61, 54, 16, 138], [3, 66], [27, 130, 91, 231], [176, 219, 107, 35]], ![[0, 83, 4, 24], [230, 63, 31, 1], [135, 36, 143, 87], [6, 78, 184, 180], [235, 5], [103, 35, 39, 144], [11, 60, 11, 204]]]
 h' := ![![[96, 62, 70], [193, 121, 133], [58, 201, 213], [101, 42, 190], [57, 102, 109], [46, 53, 148], [36, 53, 96], [0, 1]], ![[0, 176, 169], [31, 7, 91], [186, 58, 173], [145, 57, 52], [49, 230, 34], [186, 24, 122], [80, 72, 52], [96, 62, 70]], ![[0, 1], [154, 111, 15], [80, 219, 92], [216, 140, 236], [167, 146, 96], [123, 162, 208], [157, 114, 91], [0, 176, 169]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 166], []]
 b := ![[], [136, 23, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [203, 186, 143, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-421835, 540140, -188332]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1765, 2260, -788]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![16, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![16, 1, 0]] 
 ![![241, 0, 0], ![16, 1, 0], ![0, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![16, 1, 0], ![-1, 15, 3], ![51, -42, 17]]]
  hmulB := by decide  
  f := ![![![-15, -1, 0], ![241, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-15, -11, -2], ![236, 161, 0]]]
  g := ![![![1, 0, 0], ![-16, 241, 0], ![0, 0, 241]], ![![0, 1, 0], ![-1, 15, 3], ![3, -42, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![29, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![29, 1, 0]] 
 ![![241, 0, 0], ![29, 1, 0], ![211, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![29, 1, 0], ![-1, 28, 3], ![51, -42, 30]]]
  hmulB := by decide  
  f := ![![![-398, 11172, 1197], ![0, -96159, 0]], ![![-48, 1344, 144], ![1, -11568, 0]], ![![-357, 9781, 1048], ![71, -84189, 0]]]
  g := ![![![1, 0, 0], ![-29, 241, 0], ![-211, 0, 241]], ![![0, 1, 0], ![-6, 28, 3], ![-21, -42, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-45, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-45, 1, 0]] 
 ![![241, 0, 0], ![196, 1, 0], ![113, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-45, 1, 0], ![-1, -46, 3], ![51, -42, -44]]]
  hmulB := by decide  
  f := ![![![-39673, -1825004, 119022], ![0, -9561434, 0]], ![![-32264, -1484190, 96795], ![1, -7775865, 0]], ![![-18614, -855707, 55807], ![-65, -4483162, 0]]]
  g := ![![![1, 0, 0], ![-196, 241, 0], ![-113, 0, 241]], ![![-1, 1, 0], ![36, -46, 3], ![55, -42, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![16, 1, 0]] ![![241, 0, 0], ![29, 1, 0]]
  ![![241, 0, 0], ![74, 95, 1]] where
 M := ![![![58081, 0, 0], ![6989, 241, 0]], ![![3856, 241, 0], ![463, 44, 3]]]
 hmul := by decide  
 g := ![![![![167, -95, -1], ![241, 0, 0]], ![![-45, -94, -1], ![241, 0, 0]]], ![![![-58, -94, -1], ![241, 0, 0]], ![![1, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![74, 95, 1]] ![![241, 0, 0], ![-45, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-10845, 241, 0]], ![![17834, 22895, 241], ![-3374, -4338, 241]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-45, 1, 0]]], ![![![74, 95, 1]], ![![-14, -18, 1]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -4, -1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![6, -4, -1]] 
 ![![251, 0, 0], ![35, 1, 0], ![105, 0, 1]] where
  M :=![![![6, -4, -1], ![-47, 52, -13], ![-252, 165, 43]]]
  hmulB := by decide  
  f := ![![![-4381, -7, -104]], ![![-632, -1, -15]], ![![-1854, -3, -44]]]
  g := ![![![1, -4, -1], ![-2, 52, -13], ![-42, 165, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2445, 4, 58]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![2445, 4, 58]] 
 ![![251, 0, 0], ![219, 1, 0], ![66, 0, 1]] where
  M :=![![![2445, 4, 58], ![2954, 5, 70], ![2988, 6, 71]]]
  hmulB := by decide  
  f := ![![![-65, 64, -10]], ![![-59, 57, -8]], ![![-6, 6, -1]]]
  g := ![![![-9, 4, 58], ![-11, 5, 70], ![-12, 6, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![251, 0, 0], ![248, 1, 0], ![163, 0, 1]] where
  M :=![![![-3, 1, 0], ![-1, -4, 3], ![51, -42, -2]]]
  hmulB := by decide  
  f := ![![![-134, -2, -3]], ![![-133, -2, -3]], ![![-88, -1, -2]]]
  g := ![![![-1, 1, 0], ![2, -4, 3], ![43, -42, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![6, -4, -1]] ![![2445, 4, 58]]
  ![![-134, -2, -3]] where
 M := ![![![-134, -2, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-134, -2, -3]] ![![-3, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![251, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [39, 255, 247, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 34, 166], [135, 222, 91], [0, 1]]
 g := ![![[135, 49, 122], [205, 215], [142, 16], [137, 139], [240, 140], [191, 124], [10, 1], []], ![[146, 184, 125, 77], [40, 239], [241, 193], [21, 100], [108, 205], [96, 222], [184, 197], [36, 57]], ![[154, 26, 56, 186], [85, 232], [80, 213], [172, 190], [26, 244], [40, 2], [37, 128], [111, 57]]]
 h' := ![![[132, 34, 166], [90, 65, 76], [115, 102, 27], [241, 195, 253], [207, 219, 216], [217, 86, 59], [124, 238, 102], [0, 0, 1], [0, 1]], ![[135, 222, 91], [43, 228, 163], [224, 133, 53], [194, 147, 128], [146, 41, 10], [195, 53, 132], [220, 62, 215], [86, 143, 222], [132, 34, 166]], ![[0, 1], [210, 221, 18], [236, 22, 177], [23, 172, 133], [250, 254, 31], [39, 118, 66], [166, 214, 197], [18, 114, 34], [135, 222, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 206], []]
 b := ![[], [127, 109, 135], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [39, 255, 247, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104856, -95604, 13107]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![408, -372, 51]
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



lemma PB278I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB278I4 : PrimesBelowBoundCertificateInterval O 193 257 278 where
  m := 11
  g := ![3, 2, 2, 1, 2, 2, 2, 1, 3, 3, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB278I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0, I241N1, I241N2]
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
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![241, 241, 241]
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
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1, I227N1, I229N1, I233N1, I241N0, I241N1, I241N2, I251N0, I251N1, I251N2]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [], [I227N1], [I229N1], [I233N1], [], [I241N0, I241N1, I241N2], [I251N0, I251N1, I251N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
