
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![48, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![48, 1, 0]] 
 ![![197, 0, 0], ![48, 1, 0], ![60, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![48, 1, 0], ![0, 48, 1], ![558, 124, 48]]]
  hmulB := by decide  
  f := ![![![2977, 62, 0], ![-12214, 0, 0]], ![![720, 15, 0], ![-2954, 0, 0]], ![![876, 18, 0], ![-3594, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 197, 0], ![-60, 0, 197]], ![![0, 1, 0], ![-12, 48, 1], ![-42, 124, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-37, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-37, 1, 0]] 
 ![![197, 0, 0], ![160, 1, 0], ![10, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-37, 1, 0], ![0, -37, 1], ![558, 124, -37]]]
  hmulB := by decide  
  f := ![![![815, -22, 0], ![4334, 0, 0]], ![![704, -19, 0], ![3744, 0, 0]], ![![44, -1, 0], ![234, 1, 0]]]
  g := ![![![1, 0, 0], ![-160, 197, 0], ![-10, 0, 197]], ![![-1, 1, 0], ![30, -37, 1], ![-96, 124, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-11, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-11, 1, 0]] 
 ![![197, 0, 0], ![186, 1, 0], ![76, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-11, 1, 0], ![0, -11, 1], ![558, 124, -11]]]
  hmulB := by decide  
  f := ![![![221, -20, 0], ![3940, 0, 0]], ![![210, -19, 0], ![3744, 0, 0]], ![![100, -9, 0], ![1784, 1, 0]]]
  g := ![![![1, 0, 0], ![-186, 197, 0], ![-76, 0, 197]], ![![-1, 1, 0], ![10, -11, 1], ![-110, 124, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![48, 1, 0]] ![![197, 0, 0], ![-37, 1, 0]]
  ![![197, 0, 0], ![-3, 11, 1]] where
 M := ![![![38809, 0, 0], ![-7289, 197, 0]], ![![9456, 197, 0], ![-1776, 11, 1]]]
 hmul := by decide  
 g := ![![![![197, 0, 0], ![0, 0, 0]], ![![-34, -10, -1], ![197, 0, 0]]], ![![![48, 1, 0], ![0, 0, 0]], ![![-9, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![-3, 11, 1]] ![![197, 0, 0], ![-11, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-2167, 197, 0]], ![![-591, 2167, 197], ![591, 0, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-11, 1, 0]]], ![![![-3, 11, 1]], ![![3, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-139, 69, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-139, 69, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![60, 69, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-139, 69, 1], ![558, -15, 69], ![38502, 9114, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -69, 199]], ![![-1, 0, 1], ![-18, -24, 69], ![198, 51, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [117, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 198], [0, 1]]
 g := ![![[85, 182], [117, 13], [74, 131], [188], [33], [106], [5, 1]], ![[0, 17], [182, 186], [132, 68], [188], [33], [106], [10, 198]]]
 h' := ![![[5, 198], [42, 111], [98, 49], [9, 23], [151, 136], [80, 113], [12, 107], [0, 1]], ![[0, 1], [0, 88], [144, 150], [124, 176], [35, 63], [48, 86], [149, 92], [5, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [22, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [117, 194, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1233, 612, -69]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, 27, -69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-69, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-69, 1, 0]] 
 ![![199, 0, 0], ![130, 1, 0], ![15, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-69, 1, 0], ![0, -69, 1], ![558, 124, -69]]]
  hmulB := by decide  
  f := ![![![7246, -105, 0], ![20895, 0, 0]], ![![4762, -69, 0], ![13732, 0, 0]], ![![576, -8, 0], ![1661, 1, 0]]]
  g := ![![![1, 0, 0], ![-130, 199, 0], ![-15, 0, 199]], ![![-1, 1, 0], ![45, -69, 1], ![-73, 124, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-139, 69, 1]] ![![199, 0, 0], ![-69, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-13731, 199, 0]], ![![-27661, 13731, 199], ![10149, -4776, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-69, 1, 0]]], ![![![-139, 69, 1]], ![![51, -24, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![19, 96, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![19, 96, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![19, 96, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![19, 96, 1], ![558, 143, 96], ![53568, 12462, 143]]]
  hmulB := by decide  
  f := ![![![-18, -96, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -96, 211]], ![![0, 0, 1], ![-6, -43, 96], ![241, -6, 143]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [48, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 210], [0, 1]]
 g := ![![[73, 114], [70, 194], [44], [69], [64, 196], [114], [83, 1]], ![[40, 97], [136, 17], [44], [69], [85, 15], [114], [166, 210]]]
 h' := ![![[83, 210], [16, 122], [44, 48], [62, 39], [93, 160], [6, 197], [25, 89], [0, 1]], ![[0, 1], [14, 89], [19, 163], [134, 172], [80, 51], [110, 14], [27, 122], [83, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [10, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [48, 128, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6775, 3282, 1498]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-167, -666, 1498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-96, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-96, 1, 0]] 
 ![![211, 0, 0], ![115, 1, 0], ![68, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-96, 1, 0], ![0, -96, 1], ![558, 124, -96]]]
  hmulB := by decide  
  f := ![![![1825, -19, 0], ![4009, 0, 0]], ![![1153, -12, 0], ![2533, 0, 0]], ![![620, -6, 0], ![1362, 1, 0]]]
  g := ![![![1, 0, 0], ![-115, 211, 0], ![-68, 0, 211]], ![![-1, 1, 0], ![52, -96, 1], ![-34, 124, -96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![19, 96, 1]] ![![211, 0, 0], ![-96, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-20256, 211, 0]], ![![4009, 20256, 211], ![-1266, -9073, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-96, 1, 0]]], ![![![19, 96, 1]], ![![-6, -43, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![11, 71, 1]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![11, 71, 1]] 
 ![![223, 0, 0], ![0, 223, 0], ![11, 71, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![11, 71, 1], ![558, 135, 71], ![39618, 9362, 135]]]
  hmulB := by decide  
  f := ![![![-10, -71, -1], ![223, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -71, 223]], ![![0, 0, 1], ![-1, -22, 71], ![171, -1, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [60, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 222], [0, 1]]
 g := ![![[139, 197], [96, 39], [61, 63], [127, 1], [91, 37], [14], [134, 1]], ![[0, 26], [193, 184], [29, 160], [38, 222], [143, 186], [14], [45, 222]]]
 h' := ![![[134, 222], [38, 33], [131, 40], [185, 78], [115, 222], [196, 86], [211, 56], [0, 1]], ![[0, 1], [0, 190], [139, 183], [156, 145], [204, 1], [124, 137], [133, 167], [134, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [132, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [60, 89, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2656, 271, 164]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -51, 164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![-71, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![-71, 1, 0]] 
 ![![223, 0, 0], ![152, 1, 0], ![88, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![-71, 1, 0], ![0, -71, 1], ![558, 124, -71]]]
  hmulB := by decide  
  f := ![![![2415, -34, 0], ![7582, 0, 0]], ![![1634, -23, 0], ![5130, 0, 0]], ![![946, -13, 0], ![2970, 1, 0]]]
  g := ![![![1, 0, 0], ![-152, 223, 0], ![-88, 0, 223]], ![![-1, 1, 0], ![48, -71, 1], ![-54, 124, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![11, 71, 1]] ![![223, 0, 0], ![-71, 1, 0]]
  ![![223, 0, 0]] where
 M := ![![![49729, 0, 0], ![-15833, 223, 0]], ![![2453, 15833, 223], ![-223, -4906, 0]]]
 hmul := by decide  
 g := ![![![![223, 0, 0]], ![![-71, 1, 0]]], ![![![11, 71, 1]], ![![-1, -22, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-123, 1, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-123, 1, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![104, 1, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-123, 1, 1], ![558, 1, 1], ![558, 682, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -1, 227]], ![![-1, 0, 1], ![2, 0, 1], ![2, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [90, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [168, 226], [0, 1]]
 g := ![![[210, 169], [6, 173], [76], [186], [59], [18, 196], [168, 1]], ![[0, 58], [14, 54], [76], [186], [59], [31, 31], [109, 226]]]
 h' := ![![[168, 226], [141, 214], [34, 20], [219, 59], [191, 58], [196, 115], [89, 213], [0, 1]], ![[0, 1], [0, 13], [216, 207], [143, 168], [174, 169], [221, 112], [7, 14], [168, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [9, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [90, 59, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3198, 4339, 934]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-442, 15, 934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-1, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-1, 1, 0]] 
 ![![227, 0, 0], ![226, 1, 0], ![226, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-1, 1, 0], ![0, -1, 1], ![558, 124, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![681, 0, 0]], ![![2, -1, 0], ![228, 0, 0]], ![![2, -1, 0], ![228, 1, 0]]]
  g := ![![![1, 0, 0], ![-226, 227, 0], ![-226, 0, 227]], ![![-1, 1, 0], ![0, -1, 1], ![-120, 124, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-123, 1, 1]] ![![227, 0, 0], ![-1, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-227, 227, 0]], ![![-27921, 227, 227], ![681, 0, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-1, 1, 0]]], ![![![-123, 1, 1]], ![![3, 0, 0]]]]
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


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [219, 67, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 214, 150], [135, 14, 79], [0, 1]]
 g := ![![[122, 153, 68], [98, 49], [220, 137, 70], [2, 85], [32, 125], [39, 38, 132], [1]], ![[104, 3, 14, 107], [52, 215], [82, 32, 117, 190], [105, 218], [187, 204], [17, 120, 115, 59], [48, 25, 176, 227]], ![[24, 65, 37, 194], [181, 37], [115, 109, 193, 211], [190, 203], [77, 82], [140, 69, 210, 110], [194, 201, 108, 2]]]
 h' := ![![[75, 214, 150], [149, 55, 86], [139, 41, 222], [154, 50, 191], [135, 196, 90], [161, 157, 128], [10, 162, 210], [0, 1]], ![[135, 14, 79], [7, 83, 65], [113, 62, 98], [123, 79, 98], [203, 2, 203], [169, 216, 152], [79, 160, 218], [75, 214, 150]], ![[0, 1], [219, 91, 78], [87, 126, 138], [227, 100, 169], [56, 31, 165], [120, 85, 178], [107, 136, 30], [135, 14, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 50], []]
 b := ![[], [72, 180, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [219, 67, 19, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-498075, -171063, -15114]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2175, -747, -66]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![32, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![32, 1, 0]] 
 ![![233, 0, 0], ![32, 1, 0], ![141, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![32, 1, 0], ![0, 32, 1], ![558, 124, 32]]]
  hmulB := by decide  
  f := ![![![1505, 47, 0], ![-10951, 0, 0]], ![![160, 5, 0], ![-1164, 0, 0]], ![![869, 27, 0], ![-6323, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 233, 0], ![-141, 0, 233]], ![![0, 1, 0], ![-5, 32, 1], ![-34, 124, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![72, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![72, 1, 0]] 
 ![![233, 0, 0], ![72, 1, 0], ![175, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![72, 1, 0], ![0, 72, 1], ![558, 124, 72]]]
  hmulB := by decide  
  f := ![![![7201, 100, 0], ![-23300, 0, 0]], ![![2232, 31, 0], ![-7222, 0, 0]], ![![5351, 74, 0], ![-17314, 1, 0]]]
  g := ![![![1, 0, 0], ![-72, 233, 0], ![-175, 0, 233]], ![![0, 1, 0], ![-23, 72, 1], ![-90, 124, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-104, 1, 0]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-104, 1, 0]] 
 ![![233, 0, 0], ![129, 1, 0], ![135, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-104, 1, 0], ![0, -104, 1], ![558, 124, -104]]]
  hmulB := by decide  
  f := ![![![21737, -209, 0], ![48697, 0, 0]], ![![12065, -116, 0], ![27029, 0, 0]], ![![12631, -121, 0], ![28297, 1, 0]]]
  g := ![![![1, 0, 0], ![-129, 233, 0], ![-135, 0, 233]], ![![-1, 1, 0], ![57, -104, 1], ![-6, 124, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![32, 1, 0]] ![![233, 0, 0], ![72, 1, 0]]
  ![![233, 0, 0], ![-26, 104, 1]] where
 M := ![![![54289, 0, 0], ![16776, 233, 0]], ![![7456, 233, 0], ![2304, 104, 1]]]
 hmul := by decide  
 g := ![![![![233, 0, 0], ![0, 0, 0]], ![![72, 1, 0], ![0, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![10, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-26, 104, 1]] ![![233, 0, 0], ![-104, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-24232, 233, 0]], ![![-6058, 24232, 233], ![3262, -10718, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-104, 1, 0]]], ![![![-26, 104, 1]], ![![14, -46, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-106, 1, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-106, 1, 0]] 
 ![![239, 0, 0], ![133, 1, 0], ![236, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-106, 1, 0], ![0, -106, 1], ![558, 124, -106]]]
  hmulB := by decide  
  f := ![![![17067, -161, 0], ![38479, 0, 0]], ![![9541, -90, 0], ![21511, 0, 0]], ![![16796, -158, 0], ![37868, 1, 0]]]
  g := ![![![1, 0, 0], ![-133, 239, 0], ![-236, 0, 239]], ![![-1, 1, 0], ![58, -106, 1], ![38, 124, -106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N0 : Nat.card (O ⧸ I239N0) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N0)

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := prime_ideal_of_norm_prime hp239.out _ NI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-68, 1, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-68, 1, 0]] 
 ![![239, 0, 0], ![171, 1, 0], ![156, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-68, 1, 0], ![0, -68, 1], ![558, 124, -68]]]
  hmulB := by decide  
  f := ![![![10065, -148, 0], ![35372, 0, 0]], ![![7277, -107, 0], ![25574, 0, 0]], ![![6548, -96, 0], ![23012, 1, 0]]]
  g := ![![![1, 0, 0], ![-171, 239, 0], ![-156, 0, 239]], ![![-1, 1, 0], ![48, -68, 1], ![-42, 124, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0], ![-65, 1, 0]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![239, 0, 0], ![-65, 1, 0]] 
 ![![239, 0, 0], ![174, 1, 0], ![77, 0, 1]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]], ![![-65, 1, 0], ![0, -65, 1], ![558, 124, -65]]]
  hmulB := by decide  
  f := ![![![9491, -146, 0], ![34894, 0, 0]], ![![6826, -105, 0], ![25096, 0, 0]], ![![3073, -47, 0], ![11298, 1, 0]]]
  g := ![![![1, 0, 0], ![-174, 239, 0], ![-77, 0, 239]], ![![-1, 1, 0], ![47, -65, 1], ![-67, 124, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-106, 1, 0]] ![![239, 0, 0], ![-68, 1, 0]]
  ![![239, 0, 0], ![-201, 65, 1]] where
 M := ![![![57121, 0, 0], ![-16252, 239, 0]], ![![-25334, 239, 0], ![7208, -174, 1]]]
 hmul := by decide  
 g := ![![![![239, 0, 0], ![0, 0, 0]], ![![133, -64, -1], ![239, 0, 0]]], ![![![95, -64, -1], ![239, 0, 0]], ![![31, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![239, 0, 0], ![-201, 65, 1]] ![![239, 0, 0], ![-65, 1, 0]]
  ![![239, 0, 0]] where
 M := ![![![57121, 0, 0], ![-15535, 239, 0]], ![![-48039, 15535, 239], ![13623, -4302, 0]]]
 hmul := by decide  
 g := ![![![![239, 0, 0]], ![![-65, 1, 0]]], ![![![-201, 65, 1]], ![![57, -18, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-4, -19, 1]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-4, -19, 1]] 
 ![![241, 0, 0], ![0, 241, 0], ![237, 222, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-4, -19, 1], ![558, 120, -19], ![-10602, -1798, 120]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-237, -222, 241]], ![![-1, -1, 1], ![21, 18, -19], ![-162, -118, 120]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [28, 232, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 240], [0, 1]]
 g := ![![[146, 159], [169], [123], [133], [174, 221], [15, 158], [9, 1]], ![[131, 82], [169], [123], [133], [235, 20], [232, 83], [18, 240]]]
 h' := ![![[9, 240], [239, 20], [174, 13], [185, 169], [189, 186], [62, 170], [230, 53], [0, 1]], ![[0, 1], [178, 221], [50, 228], [19, 72], [176, 55], [146, 71], [225, 188], [9, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [93, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [28, 232, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21465, 9716, 719]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-618, -622, 719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![19, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![19, 1, 0]] 
 ![![241, 0, 0], ![19, 1, 0], ![121, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![19, 1, 0], ![0, 19, 1], ![558, 124, 19]]]
  hmulB := by decide  
  f := ![![![3326, 175, 0], ![-42175, 0, 0]], ![![228, 12, 0], ![-2891, 0, 0]], ![![1674, 88, 0], ![-21227, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 241, 0], ![-121, 0, 241]], ![![0, 1, 0], ![-2, 19, 1], ![-17, 124, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![-4, -19, 1]] ![![241, 0, 0], ![19, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![4579, 241, 0]], ![![-964, -4579, 241], ![482, -241, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![19, 1, 0]]], ![![![-4, -19, 1]], ![![2, -1, 0]]]]
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


lemma PB250I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 249 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 249 (by omega)

def PB250I4 : PrimesBelowBoundCertificateInterval O 193 249 250 where
  m := 9
  g := ![3, 2, 2, 2, 2, 1, 3, 3, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB250I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1]
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
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![44521, 211]
    · exact ![49729, 223]
    · exact ![51529, 227]
    · exact ![12008989]
    · exact ![233, 233, 233]
    · exact ![239, 239, 239]
    · exact ![58081, 241]
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
      exact NI223N1
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
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
  β := ![I197N0, I197N1, I197N2, I199N1, I211N1, I223N1, I227N1, I233N0, I233N1, I233N2, I239N0, I239N1, I239N2, I241N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N1], [I223N1], [I227N1], [], [I233N0, I233N1, I233N2], [I239N0, I239N1, I239N2], [I241N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
