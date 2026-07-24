
import IdealArithmetic.Examples.NF3_1_853335_2.RI3_1_853335_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![295, 50, 23]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![295, 50, 23]] 
 ![![197, 0, 0], ![0, 197, 0], ![167, 45, 1]] where
  M :=![![![295, 50, 23], ![4669, 778, 350], ![10150, 1717, 778]]]
  hmulB := by decide  
  f := ![![![22, 3, -2]], ![![-406, -20, 21]], ![![-71, -2, 3]]]
  g := ![![![-18, -5, 23], ![-273, -76, 350], ![-608, -169, 778]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [93, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 196], [0, 1]]
 g := ![![[48, 161], [104], [191, 22], [109], [132], [101], [67, 1]], ![[0, 36], [104], [89, 175], [109], [132], [101], [134, 196]]]
 h' := ![![[67, 196], [85, 84], [164, 164], [53, 131], [145, 122], [73, 59], [73, 62], [0, 1]], ![[0, 1], [0, 113], [120, 33], [162, 66], [45, 75], [86, 138], [90, 135], [67, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [105, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [93, 130, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![499, -59, -102]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![89, 23, -102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, -3, 2]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-22, -3, 2]] 
 ![![197, 0, 0], ![79, 1, 0], ![9, 0, 1]] where
  M :=![![![-22, -3, 2], ![406, 20, -21], ![-609, -5, 20]]]
  hmulB := by decide  
  f := ![![![-295, -50, -23]], ![![-142, -24, -11]], ![![-65, -11, -5]]]
  g := ![![![1, -3, 2], ![-5, 20, -21], ![-2, -5, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![295, 50, 23]] ![![-22, -3, 2]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![22, -62, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![22, -62, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![22, 137, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![22, -62, 1], ![203, 43, -434], ![-12586, -1273, 43]]]
  hmulB := by decide  
  f := ![![![-21, 62, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -137, 199]], ![![0, -1, 1], ![49, 299, -434], ![-68, -36, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [97, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 198], [0, 1]]
 g := ![![[9, 29], [116, 121], [110, 61], [157], [8], [139], [122, 1]], ![[164, 170], [152, 78], [189, 138], [157], [8], [139], [45, 198]]]
 h' := ![![[122, 198], [91, 32], [76, 11], [95, 85], [1, 117], [141, 40], [106, 61], [0, 1]], ![[0, 1], [15, 167], [25, 188], [117, 114], [146, 82], [46, 159], [185, 138], [122, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [41, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [97, 77, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2415, -141, 442]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -305, 442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![36, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![36, 1, 0]] 
 ![![199, 0, 0], ![36, 1, 0], ![156, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![36, 1, 0], ![0, 36, 7], ![203, 21, 36]]]
  hmulB := by decide  
  f := ![![![2809, 78, 0], ![-15522, 0, 0]], ![![468, 13, 0], ![-2586, 0, 0]], ![![2172, 50, -2], ![-12002, 57, 0]]]
  g := ![![![1, 0, 0], ![-36, 199, 0], ![-156, 0, 199]], ![![0, 1, 0], ![-12, 36, 7], ![-31, 21, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![22, -62, 1]] ![![199, 0, 0], ![36, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![7164, 199, 0]], ![![4378, -12338, 199], ![995, -2189, -398]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![36, 1, 0]]], ![![![22, -62, 1]], ![![5, -11, -2]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-105, 58, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-105, 58, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![106, 58, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-105, 58, 1], ![203, -84, 406], ![11774, 1247, -84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -58, 211]], ![![-1, 0, 1], ![-203, -112, 406], ![98, 29, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [107, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [184, 210], [0, 1]]
 g := ![![[18, 71], [65, 125], [105], [14], [82, 46], [121], [184, 1]], ![[0, 140], [66, 86], [105], [14], [106, 165], [121], [157, 210]]]
 h' := ![![[184, 210], [8, 55], [41, 114], [127, 152], [88, 15], [140, 62], [146, 200], [0, 1]], ![[0, 1], [0, 156], [128, 97], [32, 59], [105, 196], [154, 149], [21, 11], [184, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [63, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [107, 27, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2069, -114, 129]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55, -36, 129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![16, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![16, 1, 0]] 
 ![![211, 0, 0], ![16, 1, 0], ![84, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![16, 1, 0], ![0, 16, 7], ![203, 21, 16]]]
  hmulB := by decide  
  f := ![![![993, 62, 0], ![-13082, 0, 0]], ![![48, 3, 0], ![-632, 0, 0]], ![![380, 10, -6], ![-5006, 181, 0]]]
  g := ![![![1, 0, 0], ![-16, 211, 0], ![-84, 0, 211]], ![![0, 1, 0], ![-4, 16, 7], ![-7, 21, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-105, 58, 1]] ![![211, 0, 0], ![16, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![3376, 211, 0]], ![![-22155, 12238, 211], ![-1477, 844, 422]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![16, 1, 0]]], ![![![-105, 58, 1]], ![![-7, 4, 2]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![40, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![40, 1, 0]] 
 ![![223, 0, 0], ![40, 1, 0], ![90, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![40, 1, 0], ![0, 40, 7], ![203, 21, 40]]]
  hmulB := by decide  
  f := ![![![5201, 130, 0], ![-28990, 0, 0]], ![![920, 23, 0], ![-5128, 0, 0]], ![![2070, 46, -1], ![-11538, 32, 0]]]
  g := ![![![1, 0, 0], ![-40, 223, 0], ![-90, 0, 223]], ![![0, 1, 0], ![-10, 40, 7], ![-19, 21, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![89, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![89, 1, 0]] 
 ![![223, 0, 0], ![89, 1, 0], ![79, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![89, 1, 0], ![0, 89, 7], ![203, 21, 89]]]
  hmulB := by decide  
  f := ![![![6231, 70, 0], ![-15610, 0, 0]], ![![2403, 27, 0], ![-6020, 0, 0]], ![![2205, 12, -1], ![-5524, 32, 0]]]
  g := ![![![1, 0, 0], ![-89, 223, 0], ![-79, 0, 223]], ![![0, 1, 0], ![-38, 89, 7], ![-39, 21, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![94, 1, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![223, 0, 0], ![94, 1, 0]] 
 ![![223, 0, 0], ![94, 1, 0], ![12, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![94, 1, 0], ![0, 94, 7], ![203, 21, 94]]]
  hmulB := by decide  
  f := ![![![6863, 73, 0], ![-16279, 0, 0]], ![![2914, 31, 0], ![-6912, 0, 0]], ![![328, -10, -1], ![-778, 32, 0]]]
  g := ![![![1, 0, 0], ![-94, 223, 0], ![-12, 0, 223]], ![![0, 1, 0], ![-40, 94, 7], ![-13, 21, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![40, 1, 0]] ![![223, 0, 0], ![89, 1, 0]]
  ![![223, 0, 0], ![-33, -109, 1]] where
 M := ![![![49729, 0, 0], ![19847, 223, 0]], ![![8920, 223, 0], ![3560, 129, 7]]]
 hmul := by decide  
 g := ![![![![223, 0, 0], ![0, 0, 0]], ![![89, 1, 0], ![0, 0, 0]]], ![![![40, 1, 0], ![0, 0, 0]], ![![17, 4, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![-33, -109, 1]] ![![223, 0, 0], ![94, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![20962, 223, 0]], ![![-7359, -24307, 223], ![-2899, -10258, -669]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![94, 1, 0]]], ![![![-33, -109, 1]], ![![-13, -46, -3]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![2, 1, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![2, 1, 0]] 
 ![![227, 0, 0], ![2, 1, 0], ![194, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![2, 1, 0], ![0, 2, 7], ![203, 21, 2]]]
  hmulB := by decide  
  f := ![![![225, 112, 0], ![-25424, 0, 0]], ![![-2, -1, 0], ![228, 0, 0]], ![![190, 94, -2], ![-21468, 65, 0]]]
  g := ![![![1, 0, 0], ![-2, 227, 0], ![-194, 0, 227]], ![![0, 1, 0], ![-6, 2, 7], ![-1, 21, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N0)

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := prime_ideal_of_norm_prime hp227.out _ NI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![11, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![11, 1, 0]] 
 ![![227, 0, 0], ![11, 1, 0], ![80, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![11, 1, 0], ![0, 11, 7], ![203, 21, 11]]]
  hmulB := by decide  
  f := ![![![661, 60, 0], ![-13620, 0, 0]], ![![11, 1, 0], ![-226, 0, 0]], ![![222, 17, -2], ![-4574, 65, 0]]]
  g := ![![![1, 0, 0], ![-11, 227, 0], ![-80, 0, 227]], ![![0, 1, 0], ![-3, 11, 7], ![-4, 21, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-13, 1, 0]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-13, 1, 0]] 
 ![![227, 0, 0], ![214, 1, 0], ![138, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-13, 1, 0], ![0, -13, 7], ![203, 21, -13]]]
  hmulB := by decide  
  f := ![![![508, -39, 0], ![8853, 0, 0]], ![![482, -37, 0], ![8400, 0, 0]], ![![322, -21, -2], ![5612, 65, 0]]]
  g := ![![![1, 0, 0], ![-214, 227, 0], ![-138, 0, 227]], ![![-1, 1, 0], ![8, -13, 7], ![-11, 21, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![2, 1, 0]] ![![227, 0, 0], ![11, 1, 0]]
  ![![227, 0, 0], ![68, -63, 1]] where
 M := ![![![51529, 0, 0], ![2497, 227, 0]], ![![454, 227, 0], ![22, 13, 7]]]
 hmul := by decide  
 g := ![![![![159, 63, -1], ![227, 0, 0]], ![![-57, 64, -1], ![227, 0, 0]]], ![![![-66, 64, -1], ![227, 0, 0]], ![![-2, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![68, -63, 1]] ![![227, 0, 0], ![-13, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-2951, 227, 0]], ![![15436, -14301, 227], ![-681, 908, -454]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-13, 1, 0]]], ![![![68, -63, 1]], ![![-3, 4, -2]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-97, 1, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-97, 1, 0]] 
 ![![229, 0, 0], ![132, 1, 0], ![128, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-97, 1, 0], ![0, -97, 7], ![203, 21, -97]]]
  hmulB := by decide  
  f := ![![![12126, -125, 0], ![28625, 0, 0]], ![![7082, -73, 0], ![16718, 0, 0]], ![![6838, -15, -4], ![16142, 131, 0]]]
  g := ![![![1, 0, 0], ![-132, 229, 0], ![-128, 0, 229]], ![![-1, 1, 0], ![52, -97, 7], ![43, 21, -97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-85, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-85, 1, 0]] 
 ![![229, 0, 0], ![144, 1, 0], ![211, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-85, 1, 0], ![0, -85, 7], ![203, 21, -85]]]
  hmulB := by decide  
  f := ![![![11476, -135, 0], ![30915, 0, 0]], ![![7226, -85, 0], ![19466, 0, 0]], ![![10594, -76, -4], ![28539, 131, 0]]]
  g := ![![![1, 0, 0], ![-144, 229, 0], ![-211, 0, 229]], ![![-1, 1, 0], ![47, -85, 7], ![66, 21, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-47, 1, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-47, 1, 0]] 
 ![![229, 0, 0], ![182, 1, 0], ![77, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-47, 1, 0], ![0, -47, 7], ![203, 21, -47]]]
  hmulB := by decide  
  f := ![![![2492, -53, 0], ![12137, 0, 0]], ![![2022, -43, 0], ![9848, 0, 0]], ![![888, 8, -4], ![4325, 131, 0]]]
  g := ![![![1, 0, 0], ![-182, 229, 0], ![-77, 0, 229]], ![![-1, 1, 0], ![35, -47, 7], ![0, 21, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-97, 1, 0]] ![![229, 0, 0], ![-85, 1, 0]]
  ![![229, 0, 0], ![-98, -26, 1]] where
 M := ![![![52441, 0, 0], ![-19465, 229, 0]], ![![-22213, 229, 0], ![8245, -182, 7]]]
 hmul := by decide  
 g := ![![![![229, 0, 0], ![0, 0, 0]], ![![13, 27, -1], ![229, 0, 0]]], ![![![1, 27, -1], ![229, 0, 0]], ![![39, 0, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![-98, -26, 1]] ![![229, 0, 0], ![-47, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-10763, 229, 0]], ![![-22442, -5954, 229], ![4809, 1145, -229]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-47, 1, 0]]], ![![![-98, -26, 1]], ![![21, 5, -1]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [10, 41, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [138, 42, 55], [205, 190, 178], [0, 1]]
 g := ![![[126, 203, 1], [7, 210], [92, 18], [163, 132, 225], [147, 144], [74, 171, 217], [1]], ![[146, 27, 43, 117], [41, 89], [194, 72], [31, 221, 14, 52], [191, 152], [31, 92, 219, 210], [158, 223, 227, 13]], ![[61, 79, 33, 37], [205, 148], [5, 18], [90, 128, 225, 148], [46, 178], [30, 111, 155, 51], [93, 198, 18, 220]]]
 h' := ![![[138, 42, 55], [99, 163, 1], [13, 116, 26], [1, 170, 211], [211, 75, 218], [192, 16, 12], [223, 192, 110], [0, 1]], ![[205, 190, 178], [70, 179, 68], [108, 222, 136], [76, 34, 44], [71, 169, 110], [74, 121, 131], [116, 23, 5], [138, 42, 55]], ![[0, 1], [19, 124, 164], [111, 128, 71], [45, 29, 211], [52, 222, 138], [195, 96, 90], [185, 18, 118], [205, 190, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 149], []]
 b := ![[], [198, 200, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [10, 41, 123, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-195720, -5359, 16077]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-840, -23, 69]
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

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![62, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![62, 1, 0]] 
 ![![239, 0, 0], ![62, 1, 0], ![202, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![62, 1, 0], ![0, 62, 7], ![203, 21, 62]]]
  hmulB := by decide  
  f := ![![![1551, 25, 0], ![-5975, 0, 0]], ![![310, 5, 0], ![-1194, 0, 0]], ![![1314, -32, -6], ![-5062, 205, 0]]]
  g := ![![![1, 0, 0], ![-62, 239, 0], ![-202, 0, 239]], ![![0, 1, 0], ![-22, 62, 7], ![-57, 21, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![80, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![80, 1, 0]] 
 ![![239, 0, 0], ![80, 1, 0], ![110, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![80, 1, 0], ![0, 80, 7], ![203, 21, 80]]]
  hmulB := by decide  
  f := ![![![81, 1, 0], ![-239, 0, 0]], ![![-80, -1, 0], ![240, 0, 0]], ![![50, -68, -6], ![-148, 205, 0]]]
  g := ![![![1, 0, 0], ![-80, 239, 0], ![-110, 0, 239]], ![![0, 1, 0], ![-30, 80, 7], ![-43, 21, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![97, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![97, 1, 0]] 
 ![![239, 0, 0], ![97, 1, 0], ![124, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![97, 1, 0], ![0, 97, 7], ![203, 21, 97]]]
  hmulB := by decide  
  f := ![![![5336, 55, 0], ![-13145, 0, 0]], ![![2134, 22, 0], ![-5257, 0, 0]], ![![2736, -55, -6], ![-6740, 205, 0]]]
  g := ![![![1, 0, 0], ![-97, 239, 0], ![-124, 0, 239]], ![![0, 1, 0], ![-43, 97, 7], ![-58, 21, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![62, 1, 0]] ![![239, 0, 0], ![80, 1, 0]]
  ![![239, 0, 0], ![94, -48, 1]] where
 M := ![![![57121, 0, 0], ![19120, 239, 0]], ![![14818, 239, 0], ![4960, 142, 7]]]
 hmul := by decide  
 g := ![![![![145, 48, -1], ![239, 0, 0]], ![![-14, 49, -1], ![239, 0, 0]]], ![![![-32, 49, -1], ![239, 0, 0]], ![![18, 2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![94, -48, 1]] ![![239, 0, 0], ![97, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![23183, 239, 0]], ![![22466, -11472, 239], ![9321, -4541, -239]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![97, 1, 0]]], ![![![94, -48, 1]], ![![39, -19, -1]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-60, 116, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-60, 116, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![181, 116, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-60, 116, 1], ![203, -39, 812], ![23548, 2465, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-181, -116, 241]], ![![-1, 0, 1], ![-609, -391, 812], ![127, 29, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [85, 233, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 240], [0, 1]]
 g := ![![[136, 217], [67], [177], [2], [104, 221], [35, 200], [8, 1]], ![[185, 24], [67], [177], [2], [185, 20], [189, 41], [16, 240]]]
 h' := ![![[8, 240], [2, 82], [40, 157], [216, 30], [77, 22], [158, 71], [43, 220], [0, 1]], ![[0, 1], [176, 159], [91, 84], [215, 211], [12, 219], [3, 170], [116, 21], [8, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [227, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [85, 233, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![491, -162, -205]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![156, 98, -205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-89, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-89, 1, 0]] 
 ![![241, 0, 0], ![152, 1, 0], ![39, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-89, 1, 0], ![0, -89, 7], ![203, 21, -89]]]
  hmulB := by decide  
  f := ![![![8634, -97, 0], ![23377, 0, 0]], ![![5430, -61, 0], ![14702, 0, 0]], ![![1556, 8, -2], ![4213, 69, 0]]]
  g := ![![![1, 0, 0], ![-152, 241, 0], ![-39, 0, 241]], ![![-1, 1, 0], ![55, -89, 7], ![2, 21, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-60, 116, 1]] ![![241, 0, 0], ![-89, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-21449, 241, 0]], ![![-14460, 27956, 241], ![5543, -10363, 723]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-89, 1, 0]]], ![![![-60, 116, 1]], ![![23, -43, 3]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 22, 10]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![131, 22, 10]] 
 ![![251, 0, 0], ![97, 1, 0], ![126, 0, 1]] where
  M :=![![![131, 22, 10], ![2030, 341, 154], ![4466, 752, 341]]]
  hmulB := by decide  
  f := ![![![473, 18, -22]], ![![165, 7, -8]], ![![252, 8, -11]]]
  g := ![![![-13, 22, 10], ![-201, 341, 154], ![-444, 752, 341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N0 : Nat.card (O ⧸ I251N0) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N0)

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := prime_ideal_of_norm_prime hp251.out _ NI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -1, 1]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-18, -1, 1]] 
 ![![251, 0, 0], ![169, 1, 0], ![151, 0, 1]] where
  M :=![![![-18, -1, 1], ![203, 3, -7], ![-203, 8, 3]]]
  hmulB := by decide  
  f := ![![![65, 11, 4]], ![![47, 8, 3]], ![![48, 8, 3]]]
  g := ![![![0, -1, 1], ![3, 3, -7], ![-8, 8, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 1, 0]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-15, 1, 0]] 
 ![![251, 0, 0], ![236, 1, 0], ![183, 0, 1]] where
  M :=![![![-15, 1, 0], ![0, -15, 7], ![203, 21, -15]]]
  hmulB := by decide  
  f := ![![![78, 15, 7]], ![![79, 15, 7]], ![![69, 13, 6]]]
  g := ![![![-1, 1, 0], ![9, -15, 7], ![-8, 21, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![131, 22, 10]] ![![-18, -1, 1]]
  ![![78, 15, 7]] where
 M := ![![![78, 15, 7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![78, 15, 7]] ![![-15, 1, 0]]
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


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [56, 140, 212, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [187, 145, 59], [115, 111, 198], [0, 1]]
 g := ![![[194, 78, 198], [223, 137], [228, 211], [232, 153], [109, 64], [51, 200], [45, 1], []], ![[72, 176, 86, 240], [16, 235], [213, 117], [211, 116], [95, 246], [109, 16], [49, 242], [23, 140]], ![[129, 45, 72, 193], [172, 173], [210, 25], [227, 223], [4, 89], [160, 42], [49, 208], [141, 140]]]
 h' := ![![[187, 145, 59], [233, 113, 202], [223, 50, 213], [150, 62, 89], [99, 96, 47], [158, 125, 249], [50, 69, 86], [0, 0, 1], [0, 1]], ![[115, 111, 198], [34, 10, 48], [219, 61, 122], [140, 232, 173], [205, 17, 87], [34, 183, 62], [22, 237, 253], [14, 251, 111], [187, 145, 59]], ![[0, 1], [6, 134, 7], [227, 146, 179], [200, 220, 252], [233, 144, 123], [171, 206, 203], [81, 208, 175], [189, 6, 145], [115, 111, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [240, 88], []]
 b := ![[], [203, 197, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [56, 140, 212, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11654436, 1443055, 719600]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45348, 5615, 2800]
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
  g := ![2, 2, 2, 3, 3, 3, 1, 3, 2, 3, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB262I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1]
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
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![227, 227, 227]
    · exact ![229, 229, 229]
    · exact ![12649337]
    · exact ![239, 239, 239]
    · exact ![58081, 241]
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
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
  β := ![I197N1, I199N1, I211N1, I223N0, I223N1, I223N2, I227N0, I227N1, I227N2, I229N0, I229N1, I229N2, I239N0, I239N1, I239N2, I241N1, I251N0, I251N1, I251N2]
  Il := ![[I197N1], [I199N1], [I211N1], [I223N0, I223N1, I223N2], [I227N0, I227N1, I227N2], [I229N0, I229N1, I229N2], [], [I239N0, I239N1, I239N2], [I241N1], [I251N0, I251N1, I251N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
