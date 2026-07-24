
import IdealArithmetic.Examples.NF3_1_905324_3.RI3_1_905324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![197, 0, 0], ![1, 1, 0], ![196, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![182, -14, 1]]]
  hmulB := by decide  
  f := ![![![15, -1, 1]], ![![1, 0, 0]], ![![14, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, -14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![13, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![13, 1, 0]] 
 ![![197, 0, 0], ![13, 1, 0], ![28, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![13, 1, 0], ![0, 13, 1], ![182, -14, 13]]]
  hmulB := by decide  
  f := ![![![1106, 85, 0], ![-16745, 0, 0]], ![![52, 4, 0], ![-787, 0, 0]], ![![144, 11, 0], ![-2180, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 197, 0], ![-28, 0, 197]], ![![0, 1, 0], ![-1, 13, 1], ![0, -14, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-14, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-14, 1, 0]] 
 ![![197, 0, 0], ![183, 1, 0], ![1, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-14, 1, 0], ![0, -14, 1], ![182, -14, -14]]]
  hmulB := by decide  
  f := ![![![2591, -185, 0], ![36445, 0, 0]], ![![2409, -172, 0], ![33885, 0, 0]], ![![15, -1, 0], ![211, 1, 0]]]
  g := ![![![1, 0, 0], ![-183, 197, 0], ![-1, 0, 197]], ![![-1, 1, 0], ![13, -14, 1], ![14, -14, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![197, 0, 0], ![13, 1, 0]]
  ![![197, 0, 0], ![13, 14, 1]] where
 M := ![![![197, 197, 0], ![13, 14, 1]]]
 hmul := by decide  
 g := ![![![![-12, -13, -1], ![197, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![13, 14, 1]] ![![197, 0, 0], ![-14, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-2758, 197, 0]], ![![2561, 2758, 197], ![0, -197, 0]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-14, 1, 0]]], ![![![13, 14, 1]], ![![0, -1, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![67, 1, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![67, 1, 0]] 
 ![![199, 0, 0], ![67, 1, 0], ![88, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![67, 1, 0], ![0, 67, 1], ![182, -14, 67]]]
  hmulB := by decide  
  f := ![![![4624, 69, 0], ![-13731, 0, 0]], ![![1474, 22, 0], ![-4377, 0, 0]], ![![1966, 29, 0], ![-5838, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 199, 0], ![-88, 0, 199]], ![![0, 1, 0], ![-23, 67, 1], ![-24, -14, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N0)

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := prime_ideal_of_norm_prime hp199.out _ NI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-35, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-35, 1, 0]] 
 ![![199, 0, 0], ![164, 1, 0], ![168, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-35, 1, 0], ![0, -35, 1], ![182, -14, -35]]]
  hmulB := by decide  
  f := ![![![3816, -109, 0], ![21691, 0, 0]], ![![3116, -89, 0], ![17712, 0, 0]], ![![3192, -91, 0], ![18144, 1, 0]]]
  g := ![![![1, 0, 0], ![-164, 199, 0], ![-168, 0, 199]], ![![-1, 1, 0], ![28, -35, 1], ![42, -14, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-32, 1, 0]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-32, 1, 0]] 
 ![![199, 0, 0], ![167, 1, 0], ![170, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-32, 1, 0], ![0, -32, 1], ![182, -14, -32]]]
  hmulB := by decide  
  f := ![![![2241, -70, 0], ![13930, 0, 0]], ![![1889, -59, 0], ![11742, 0, 0]], ![![1926, -60, 0], ![11972, 1, 0]]]
  g := ![![![1, 0, 0], ![-167, 199, 0], ![-170, 0, 199]], ![![-1, 1, 0], ![26, -32, 1], ![40, -14, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![67, 1, 0]] ![![199, 0, 0], ![-35, 1, 0]]
  ![![199, 0, 0], ![43, 32, 1]] where
 M := ![![![39601, 0, 0], ![-6965, 199, 0]], ![![13333, 199, 0], ![-2345, 32, 1]]]
 hmul := by decide  
 g := ![![![![156, -32, -1], ![199, 0, 0]], ![![-35, 1, 0], ![0, 0, 0]]], ![![![24, -31, -1], ![199, 0, 0]], ![![-12, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![43, 32, 1]] ![![199, 0, 0], ![-32, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-6368, 199, 0]], ![![8557, 6368, 199], ![-1194, -995, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-32, 1, 0]]], ![![![43, 32, 1]], ![![-6, -5, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![72, 67, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![72, 67, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![72, 67, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![72, 67, 1], ![182, 58, 67], ![12194, -756, 58]]]
  hmulB := by decide  
  f := ![![![-71, -67, -1], ![211, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -67, 211]], ![![0, 0, 1], ![-22, -21, 67], ![38, -22, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [10, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [153, 210], [0, 1]]
 g := ![![[48, 125], [33, 62], [20], [171], [84, 4], [62], [153, 1]], ![[183, 86], [24, 149], [20], [171], [63, 207], [62], [95, 210]]]
 h' := ![![[153, 210], [92, 97], [47, 189], [205, 81], [4, 63], [79, 2], [158, 189], [0, 1]], ![[0, 1], [163, 114], [57, 22], [149, 130], [148, 148], [174, 209], [168, 22], [153, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [204, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [10, 58, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![374, 96, -71]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 23, -71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![-67, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![-67, 1, 0]] 
 ![![211, 0, 0], ![144, 1, 0], ![153, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![-67, 1, 0], ![0, -67, 1], ![182, -14, -67]]]
  hmulB := by decide  
  f := ![![![5964, -89, 0], ![18779, 0, 0]], ![![4088, -61, 0], ![12872, 0, 0]], ![![4310, -64, 0], ![13571, 1, 0]]]
  g := ![![![1, 0, 0], ![-144, 211, 0], ![-153, 0, 211]], ![![-1, 1, 0], ![45, -67, 1], ![59, -14, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![72, 67, 1]] ![![211, 0, 0], ![-67, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![-14137, 211, 0]], ![![15192, 14137, 211], ![-4642, -4431, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![-67, 1, 0]]], ![![![72, 67, 1]], ![![-22, -21, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![14, 1, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0], ![14, 1, 0]] 
 ![![223, 0, 0], ![14, 1, 0], ![27, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![14, 1, 0], ![0, 14, 1], ![182, -14, 14]]]
  hmulB := by decide  
  f := ![![![197, 14, 0], ![-3122, 0, 0]], ![![-14, -1, 0], ![224, 0, 0]], ![![1, 0, 0], ![-14, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 223, 0], ![-27, 0, 223]], ![![0, 1, 0], ![-1, 14, 1], ![0, -14, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0], ![102, 1, 0]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![223, 0, 0], ![102, 1, 0]] 
 ![![223, 0, 0], ![102, 1, 0], ![77, 0, 1]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]], ![![102, 1, 0], ![0, 102, 1], ![182, -14, 102]]]
  hmulB := by decide  
  f := ![![![7243, 71, 0], ![-15833, 0, 0]], ![![3366, 33, 0], ![-7358, 0, 0]], ![![2393, 23, 0], ![-5231, 1, 0]]]
  g := ![![![1, 0, 0], ![-102, 223, 0], ![-77, 0, 223]], ![![0, 1, 0], ![-47, 102, 1], ![-28, -14, 102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![9, -2, 0]] 
 ![![223, 0, 0], ![107, 1, 0], ![147, 0, 1]] where
  M :=![![![9, -2, 0], ![0, 9, -2], ![-364, 28, 9]]]
  hmulB := by decide  
  f := ![![![-137, -18, -4]], ![![-69, -9, -2]], ![![-105, -14, -3]]]
  g := ![![![1, -2, 0], ![-3, 9, -2], ![-21, 28, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![223, 0, 0], ![14, 1, 0]] ![![223, 0, 0], ![102, 1, 0]]
  ![![-137, -18, -4]] where
 M := ![![![49729, 0, 0], ![22746, 223, 0]], ![![3122, 223, 0], ![1428, 116, 1]]]
 hmul := by decide  
 g := ![![![![2007, -446, 0]], ![![918, -195, -2]]], ![![![126, -19, -2]], ![![56, -8, -1]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-137, -18, -4]] ![![9, -2, 0]]
  ![![223, 0, 0]] where
 M := ![![![223, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![111, 18, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![111, 18, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![111, 18, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![111, 18, 1], ![182, 97, 18], ![3276, -70, 97]]]
  hmulB := by decide  
  f := ![![![-110, -18, -1], ![227, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -18, 227]], ![![0, 0, 1], ![-8, -1, 18], ![-33, -8, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [173, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 226], [0, 1]]
 g := ![![[124, 21], [130, 33], [69], [203], [3], [217, 63], [113, 1]], ![[0, 206], [0, 194], [69], [203], [3], [72, 164], [226, 226]]]
 h' := ![![[113, 226], [210, 193], [92, 184], [15, 117], [67, 138], [141, 50], [200, 111], [0, 1]], ![[0, 1], [0, 34], [0, 43], [70, 110], [225, 89], [116, 177], [31, 116], [113, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [37, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [173, 114, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2124, 1582, 214]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-114, -10, 214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-18, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-18, 1, 0]] 
 ![![227, 0, 0], ![209, 1, 0], ![130, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-18, 1, 0], ![0, -18, 1], ![182, -14, -18]]]
  hmulB := by decide  
  f := ![![![3097, -172, 0], ![39044, 0, 0]], ![![2863, -159, 0], ![36094, 0, 0]], ![![1766, -98, 0], ![22264, 1, 0]]]
  g := ![![![1, 0, 0], ![-209, 227, 0], ![-130, 0, 227]], ![![-1, 1, 0], ![16, -18, 1], ![24, -14, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![111, 18, 1]] ![![227, 0, 0], ![-18, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-4086, 227, 0]], ![![25197, 4086, 227], ![-1816, -227, 0]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-18, 1, 0]]], ![![![111, 18, 1]], ![![-8, -1, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![82, 86, 1]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![82, 86, 1]] 
 ![![229, 0, 0], ![0, 229, 0], ![82, 86, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![82, 86, 1], ![182, 68, 86], ![15652, -1022, 68]]]
  hmulB := by decide  
  f := ![![![-81, -86, -1], ![229, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -86, 229]], ![![0, 0, 1], ![-30, -32, 86], ![44, -30, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [139, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 228], [0, 1]]
 g := ![![[131, 4], [43], [72, 5], [75], [192], [172, 193], [111, 1]], ![[117, 225], [43], [169, 224], [75], [192], [69, 36], [222, 228]]]
 h' := ![![[111, 228], [21, 227], [68, 172], [165, 163], [96, 103], [137, 119], [143, 45], [0, 1]], ![[0, 1], [28, 2], [153, 57], [167, 66], [79, 126], [64, 110], [100, 184], [111, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [201, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [139, 118, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3681, 200, -3]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, 2, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-86, 1, 0]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-86, 1, 0]] 
 ![![229, 0, 0], ![143, 1, 0], ![161, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-86, 1, 0], ![0, -86, 1], ![182, -14, -86]]]
  hmulB := by decide  
  f := ![![![1205, -14, 0], ![3206, 0, 0]], ![![775, -9, 0], ![2062, 0, 0]], ![![893, -10, 0], ![2376, 1, 0]]]
  g := ![![![1, 0, 0], ![-143, 229, 0], ![-161, 0, 229]], ![![-1, 1, 0], ![53, -86, 1], ![70, -14, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![229, 0, 0], ![82, 86, 1]] ![![229, 0, 0], ![-86, 1, 0]]
  ![![229, 0, 0]] where
 M := ![![![52441, 0, 0], ![-19694, 229, 0]], ![![18778, 19694, 229], ![-6870, -7328, 0]]]
 hmul := by decide  
 g := ![![![![229, 0, 0]], ![![-86, 1, 0]]], ![![![82, 86, 1]], ![![-30, -32, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-62, -33, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-62, -33, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![171, 200, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-62, -33, 1], ![182, -76, -33], ![-6006, 644, -76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-171, -200, 233]], ![![-1, -1, 1], ![25, 28, -33], ![30, 68, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [20, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 232], [0, 1]]
 g := ![![[87, 52], [126], [71], [166, 105], [203], [211, 18], [124, 1]], ![[11, 181], [126], [71], [138, 128], [203], [113, 215], [15, 232]]]
 h' := ![![[124, 232], [152, 127], [80, 91], [175, 49], [111, 173], [207, 73], [83, 211], [0, 1]], ![[0, 1], [56, 106], [180, 142], [193, 184], [127, 60], [172, 160], [151, 22], [124, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [216]]
 b := ![[], [61, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [20, 109, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-962, 1833, -458]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![332, 401, -458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![33, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![33, 1, 0]] 
 ![![233, 0, 0], ![33, 1, 0], ![76, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![33, 1, 0], ![0, 33, 1], ![182, -14, 33]]]
  hmulB := by decide  
  f := ![![![3202, 97, 0], ![-22601, 0, 0]], ![![396, 12, 0], ![-2795, 0, 0]], ![![1028, 31, 0], ![-7256, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 233, 0], ![-76, 0, 233]], ![![0, 1, 0], ![-5, 33, 1], ![-8, -14, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![-62, -33, 1]] ![![233, 0, 0], ![33, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![7689, 233, 0]], ![![-14446, -7689, 233], ![-1864, -1165, 0]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![33, 1, 0]]], ![![![-62, -33, 1]], ![![-8, -5, 0]]]]
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


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [4, 142, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 52, 101], [209, 186, 138], [0, 1]]
 g := ![![[105, 22, 204], [96, 84, 1], [183, 101, 155], [41, 63, 216], [116, 75], [189, 138, 67], [1]], ![[193, 40, 17, 213], [204, 190, 148, 4], [202, 70, 100, 68], [137, 80, 210, 54], [97, 31], [144, 18, 140, 166], [113, 132, 27, 211]], ![[35, 98, 171, 168], [182, 2, 224, 39], [15, 40, 129, 112], [59, 148, 58, 7], [158, 180], [231, 155, 139, 140], [215, 79, 201, 28]]]
 h' := ![![[58, 52, 101], [94, 119, 193], [224, 28, 1], [75, 64, 148], [101, 143, 132], [200, 111, 187], [235, 97, 28], [0, 1]], ![[209, 186, 138], [66, 11, 117], [149, 16, 146], [178, 50, 54], [183, 191, 38], [103, 109, 105], [114, 96, 187], [58, 52, 101]], ![[0, 1], [52, 109, 168], [149, 195, 92], [1, 125, 37], [235, 144, 69], [110, 19, 186], [103, 46, 24], [209, 186, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 80], []]
 b := ![[], [153, 175, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [4, 142, 211, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51146, 36328, -3585]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![214, 152, -15]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![6, 1, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0], ![6, 1, 0]] 
 ![![241, 0, 0], ![6, 1, 0], ![205, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![6, 1, 0], ![0, 6, 1], ![182, -14, 6]]]
  hmulB := by decide  
  f := ![![![1147, 191, 0], ![-46031, 0, 0]], ![![18, 3, 0], ![-722, 0, 0]], ![![979, 163, 0], ![-39289, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 241, 0], ![-205, 0, 241]], ![![0, 1, 0], ![-1, 6, 1], ![-4, -14, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N0 : Nat.card (O ⧸ I241N0) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N0)

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := prime_ideal_of_norm_prime hp241.out _ NI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![18, 1, 0]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![241, 0, 0], ![18, 1, 0]] 
 ![![241, 0, 0], ![18, 1, 0], ![158, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![18, 1, 0], ![0, 18, 1], ![182, -14, 18]]]
  hmulB := by decide  
  f := ![![![1135, 63, 0], ![-15183, 0, 0]], ![![54, 3, 0], ![-722, 0, 0]], ![![758, 42, 0], ![-10140, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 241, 0], ![-158, 0, 241]], ![![0, 1, 0], ![-2, 18, 1], ![-10, -14, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0], ![-24, 1, 0]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![241, 0, 0], ![-24, 1, 0]] 
 ![![241, 0, 0], ![217, 1, 0], ![147, 0, 1]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]], ![![-24, 1, 0], ![0, -24, 1], ![182, -14, -24]]]
  hmulB := by decide  
  f := ![![![5593, -233, 0], ![56153, 0, 0]], ![![5041, -210, 0], ![50611, 0, 0]], ![![3435, -143, 0], ![34487, 1, 0]]]
  g := ![![![1, 0, 0], ![-217, 241, 0], ![-147, 0, 241]], ![![-1, 1, 0], ![21, -24, 1], ![28, -14, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![6, 1, 0]] ![![241, 0, 0], ![18, 1, 0]]
  ![![241, 0, 0], ![108, 24, 1]] where
 M := ![![![58081, 0, 0], ![4338, 241, 0]], ![![1446, 241, 0], ![108, 24, 1]]]
 hmul := by decide  
 g := ![![![![133, -24, -1], ![241, 0, 0]], ![![-90, -23, -1], ![241, 0, 0]]], ![![![-102, -23, -1], ![241, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![241, 0, 0], ![108, 24, 1]] ![![241, 0, 0], ![-24, 1, 0]]
  ![![241, 0, 0]] where
 M := ![![![58081, 0, 0], ![-5784, 241, 0]], ![![26028, 5784, 241], ![-2410, -482, 0]]]
 hmul := by decide  
 g := ![![![![241, 0, 0]], ![![-24, 1, 0]]], ![![![108, 24, 1]], ![![-10, -2, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -3, 1]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![23, -3, 1]] 
 ![![251, 0, 0], ![0, 251, 0], ![23, 248, 1]] where
  M :=![![![23, -3, 1], ![182, 9, -3], ![-546, 224, 9]]]
  hmulB := by decide  
  f := ![![![3, 1, 0]], ![![0, 3, 1]], ![![1, 3, 1]]]
  g := ![![![0, -1, 1], ![1, 3, -3], ![-3, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 2 2 7 [124, 229, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 250], [0, 1]]
 g := ![![[182, 83], [185, 3], [68], [89, 73], [116, 181], [6, 84], [22, 1]], ![[0, 168], [0, 248], [68], [189, 178], [82, 70], [97, 167], [44, 250]]]
 h' := ![![[22, 250], [152, 130], [166, 175], [8, 90], [174, 18], [9, 92], [33, 109], [0, 1]], ![[0, 1], [0, 121], [0, 76], [231, 161], [68, 233], [25, 159], [172, 142], [22, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [40, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 2
  hpos := by decide
  P := [124, 229, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7270, 4039, 578]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -555, 578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 63001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![251, 0, 0], ![3, 1, 0], ![242, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![182, -14, 3]]]
  hmulB := by decide  
  f := ![![![23, -3, 1]], ![![1, 0, 0]], ![![20, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-2, -14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![23, -3, 1]] ![![3, 1, 0]]
  ![![251, 0, 0]] where
 M := ![![![251, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![64, 43, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![64, 43, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![64, 43, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![64, 43, 1], ![182, 50, 43], ![7826, -420, 50]]]
  hmulB := by decide  
  f := ![![![-63, -43, -1], ![257, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -43, 257]], ![![0, 0, 1], ![-10, -7, 43], ![18, -10, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [130, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [204, 256], [0, 1]]
 g := ![![[121, 129], [253], [81], [9], [128], [29], [239], [1]], ![[223, 128], [253], [81], [9], [128], [29], [239], [1]]]
 h' := ![![[204, 256], [56, 30], [43, 225], [251, 9], [176, 254], [25, 223], [222, 85], [127, 204], [0, 1]], ![[0, 1], [8, 227], [197, 32], [31, 248], [78, 3], [28, 34], [86, 172], [109, 53], [204, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [120, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [130, 53, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1014, 419, -56]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 11, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-43, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-43, 1, 0]] 
 ![![257, 0, 0], ![214, 1, 0], ![207, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-43, 1, 0], ![0, -43, 1], ![182, -14, -43]]]
  hmulB := by decide  
  f := ![![![345, -8, 0], ![2056, 0, 0]], ![![302, -7, 0], ![1800, 0, 0]], ![![309, -7, 0], ![1842, 1, 0]]]
  g := ![![![1, 0, 0], ![-214, 257, 0], ![-207, 0, 257]], ![![-1, 1, 0], ![35, -43, 1], ![47, -14, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![64, 43, 1]] ![![257, 0, 0], ![-43, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![-11051, 257, 0]], ![![16448, 11051, 257], ![-2570, -1799, 0]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![-43, 1, 0]]], ![![![64, 43, 1]], ![![-10, -7, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB270I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB270I4 : PrimesBelowBoundCertificateInterval O 193 257 270 where
  m := 11
  g := ![3, 3, 2, 3, 2, 2, 2, 1, 3, 2, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB270I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1]
    · exact ![I257N0, I257N1]
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
    · exact ![199, 199, 199]
    · exact ![44521, 211]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![13651919]
    · exact ![241, 241, 241]
    · exact ![63001, 251]
    · exact ![66049, 257]
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
      exact NI199N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N0, I197N1, I197N2, I199N0, I199N1, I199N2, I211N1, I223N0, I223N1, I223N2, I227N1, I229N1, I233N1, I241N0, I241N1, I241N2, I251N1, I257N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N0, I199N1, I199N2], [I211N1], [I223N0, I223N1, I223N2], [I227N1], [I229N1], [I233N1], [], [I241N0, I241N1, I241N2], [I251N1], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
