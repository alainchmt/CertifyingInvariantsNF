
import IdealArithmetic.Examples.NF3_3_902356_1.RI3_3_902356_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77855, 432, 2214]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-77855, 432, 2214]] 
 ![![37, 0, 0], ![22, 1, 0], ![25, 0, 1]] where
  M :=![![![-77855, 432, 2214], ![864, 67, -54], ![30996, -378, -797]]]
  hmulB := by decide  
  f := ![![![-73811, -492588, -171666]], ![![-70514, -470585, -163998]], ![![-114827, -766314, -267059]]]
  g := ![![![-3857, 432, 2214], ![20, 67, -54], ![1601, -378, -797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2891, 19, 81]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-2891, 19, 81]] 
 ![![37, 0, 0], ![26, 1, 0], ![8, 0, 1]] where
  M :=![![![-2891, 19, 81], ![38, -37, 14], ![1134, 98, -75]]]
  hmulB := by decide  
  f := ![![![-1403, -9363, -3263]], ![![-1492, -9957, -3470]], ![![-1538, -10264, -3577]]]
  g := ![![![-109, 19, 81], ![24, -37, 14], ![-22, 98, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-77855, 432, 2214]] ![![-2891, 19, 81]]
  ![![227605897, -1278257, -6466257]] where
 M := ![![![227605897, -1278257, -6466257]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![227605897, -1278257, -6466257]] ![![-2891, 19, 81]]
  ![![37, 0, 0]] where
 M := ![![![-665389957431, 3738114366, 18903151334]]]
 hmul := by decide  
 g := ![![![![-17983512363, 101030118, 510895982]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 700, 244]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![103, 700, 244]] 
 ![![41, 0, 0], ![0, 41, 0], ![10, 19, 1]] where
  M :=![![![103, 700, 244], ![1400, 9343, 3256], ![3416, 22792, 7943]]]
  hmulB := by decide  
  f := ![![![-17, -28, 12]], ![![-56, 375, -152]], ![![-26, 141, -57]]]
  g := ![![![-57, -96, 244], ![-760, -1281, 3256], ![-1854, -3125, 7943]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [13, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 40], [0, 1]]
 g := ![![[28, 31], [32], [2], [36, 25], [1]], ![[19, 10], [32], [2], [38, 16], [1]]]
 h' := ![![[5, 40], [37, 21], [17, 14], [24, 24], [28, 5], [0, 1]], ![[0, 1], [19, 20], [5, 27], [21, 17], [12, 36], [5, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [15, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [13, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![303, 465, 715]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-167, -320, 715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -28, 12]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-17, -28, 12]] 
 ![![41, 0, 0], ![29, 1, 0], ![15, 0, 1]] where
  M :=![![![-17, -28, 12], ![-56, 375, -152], ![168, -1064, 431]]]
  hmulB := by decide  
  f := ![![![103, 700, 244]], ![![107, 723, 252]], ![![121, 812, 283]]]
  g := ![![![15, -28, 12], ![-211, 375, -152], ![599, -1064, 431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![103, 700, 244]] ![![-17, -28, 12]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [26, 16, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 26, 9], [42, 16, 34], [0, 1]]
 g := ![![[14, 36, 11], [25, 30, 6], [16, 10], [38, 22, 1], []], ![[37, 4, 30, 38], [26, 4, 3, 4], [10, 17], [23, 41, 18, 25], [14, 38]], ![[40, 18, 15, 8], [11, 41, 6, 26], [17, 16], [20, 34, 28, 22], [32, 38]]]
 h' := ![![[23, 26, 9], [38, 34, 21], [15, 5, 7], [1, 24, 28], [0, 0, 1], [0, 1]], ![[42, 16, 34], [28, 32, 40], [38, 18, 28], [13, 4, 19], [36, 27, 16], [23, 26, 9]], ![[0, 1], [11, 20, 25], [41, 20, 8], [15, 15, 39], [29, 16, 26], [42, 16, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 35], []]
 b := ![[], [16, 38, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [26, 16, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1162462, -1119118, 2954315]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27034, -26026, 68705]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [1, 33, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 26, 16], [30, 20, 31], [0, 1]]
 g := ![![[44, 26, 14], [0, 23, 7], [12, 25, 3], [22, 33, 1], []], ![[33, 13, 33, 37], [9, 18, 43, 28], [30, 20, 31, 25], [8, 9, 28, 8], [21, 21]], ![[11, 7, 18, 29], [40, 39, 29, 30], [14, 33, 25, 31], [15, 35, 31, 41], [6, 21]]]
 h' := ![![[3, 26, 16], [0, 27, 25], [35, 16, 17], [25, 40, 12], [0, 0, 1], [0, 1]], ![[30, 20, 31], [16, 6, 39], [20, 1, 32], [1, 31, 34], [35, 6, 20], [3, 26, 16]], ![[0, 1], [36, 14, 30], [15, 30, 45], [15, 23, 1], [1, 41, 26], [30, 20, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 42], []]
 b := ![[], [28, 39, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [1, 33, 14, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1267472547, -3166421302, -3097332759]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26967501, -67370666, -65900697]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -55, -16]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-7, -55, -16]] 
 ![![53, 0, 0], ![0, 53, 0], ![17, 20, 1]] where
  M :=![![![-7, -55, -16], ![-110, -622, -259], ![-224, -1813, -512]]]
  hmulB := by decide  
  f := ![![![-2851, 16, 81]], ![![32, 0, -1]], ![![-881, 5, 25]]]
  g := ![![![5, 5, -16], ![81, 86, -259], ![160, 159, -512]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [27, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 52], [0, 1]]
 g := ![![[15, 37], [11], [31, 4], [44], [19, 1]], ![[29, 16], [11], [1, 49], [44], [38, 52]]]
 h' := ![![[19, 52], [36, 14], [11, 8], [2, 2], [17, 16], [0, 1]], ![[0, 1], [37, 39], [4, 45], [40, 51], [3, 37], [19, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [47, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [27, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2250, -296, 5582]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1748, -2112, 5582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2851, 16, 81]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-2851, 16, 81]] 
 ![![53, 0, 0], ![7, 1, 0], ![21, 0, 1]] where
  M :=![![![-2851, 16, 81], ![32, 0, -1], ![1134, -7, -32]]]
  hmulB := by decide  
  f := ![![![-7, -55, -16]], ![![-3, -19, -7]], ![![-7, -56, -16]]]
  g := ![![![-88, 16, 81], ![1, 0, -1], ![35, -7, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-7, -55, -16]] ![![-2851, 16, 81]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-511, 3295, -1335]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-511, 3295, -1335]] 
 ![![59, 0, 0], ![0, 59, 0], ![17, 13, 1]] where
  M :=![![![-511, 3295, -1335], ![6590, -43941, 17810], ![-18690, 124670, -50531]]]
  hmulB := by decide  
  f := ![![![-169, -1105, -385]], ![![-2210, -14749, -5140]], ![![-627, -4178, -1456]]]
  g := ![![![376, 350, -1335], ![-5020, -4669, 17810], ![14243, 13247, -50531]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [8, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 58], [0, 1]]
 g := ![![[26, 21], [42, 17], [29], [6, 22], [28, 1]], ![[24, 38], [46, 42], [29], [32, 37], [56, 58]]]
 h' := ![![[28, 58], [18, 27], [7, 28], [11, 18], [12, 9], [0, 1]], ![[0, 1], [7, 32], [24, 31], [43, 41], [28, 50], [28, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [6, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [8, 31, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![308, 475, 740]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-208, -155, 740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-169, -1105, -385]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-169, -1105, -385]] 
 ![![59, 0, 0], ![54, 1, 0], ![20, 0, 1]] where
  M :=![![![-169, -1105, -385], ![-2210, -14749, -5140], ![-5390, -35980, -12539]]]
  hmulB := by decide  
  f := ![![![-511, 3295, -1335]], ![![-356, 2271, -920]], ![![-490, 3230, -1309]]]
  g := ![![![1139, -1105, -385], ![15204, -14749, -5140], ![37090, -35980, -12539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-511, 3295, -1335]] ![![-169, -1105, -385]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -548, -191]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-81, -548, -191]] 
 ![![61, 0, 0], ![0, 61, 0], ![33, 38, 1]] where
  M :=![![![-81, -548, -191], ![-1096, -7314, -2549], ![-2674, -17843, -6218]]]
  hmulB := by decide  
  f := ![![![55, -9, 2]], ![![-18, 116, -47]], ![![19, 62, -26]]]
  g := ![![![102, 110, -191], ![1361, 1468, -2549], ![3320, 3581, -6218]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [27, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 60], [0, 1]]
 g := ![![[37, 52], [46], [59, 39], [9, 13], [38, 1]], ![[0, 9], [46], [16, 22], [15, 48], [15, 60]]]
 h' := ![![[38, 60], [27, 33], [54, 31], [1, 51], [11, 14], [0, 1]], ![[0, 1], [0, 28], [12, 30], [48, 10], [55, 47], [38, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [14, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [27, 23, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1673, 10997, 3829]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2044, -2205, 3829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -9, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![55, -9, 2]] 
 ![![61, 0, 0], ![55, 1, 0], ![31, 0, 1]] where
  M :=![![![55, -9, 2], ![-18, 116, -47], ![28, -329, 134]]]
  hmulB := by decide  
  f := ![![![-81, -548, -191]], ![![-91, -614, -214]], ![![-85, -571, -199]]]
  g := ![![![8, -9, 2], ![-81, 116, -47], ![229, -329, 134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-81, -548, -191]] ![![55, -9, 2]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3523, -20, -100]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![3523, -20, -100]] 
 ![![67, 0, 0], ![9, 1, 0], ![36, 0, 1]] where
  M :=![![![3523, -20, -100], ![-40, 3, 0], ![-1400, 0, 43]]]
  hmulB := by decide  
  f := ![![![129, 860, 300]], ![![43, 287, 100]], ![![132, 880, 307]]]
  g := ![![![109, -20, -100], ![-1, 3, 0], ![-44, 0, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -6, -2]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1, -6, -2]] 
 ![![67, 0, 0], ![29, 1, 0], ![14, 0, 1]] where
  M :=![![![-1, -6, -2], ![-12, -77, -28], ![-28, -196, -65]]]
  hmulB := by decide  
  f := ![![![-483, 2, 14]], ![![-209, 1, 6]], ![![-98, 0, 3]]]
  g := ![![![3, -6, -2], ![39, -77, -28], ![98, -196, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![3523, -20, -100]] ![![-1, -6, -2]]
  ![![-483, 2, 14]] where
 M := ![![![-483, 2, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-483, 2, 14]] ![![-1, -6, -2]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -7, -2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-3, -7, -2]] 
 ![![71, 0, 0], ![0, 71, 0], ![37, 39, 1]] where
  M :=![![![-3, -7, -2], ![-14, -80, -33], ![-28, -231, -66]]]
  hmulB := by decide  
  f := ![![![-33, 0, 1]], ![![0, 2, -1]], ![![-17, 1, 0]]]
  g := ![![![1, 1, -2], ![17, 17, -33], ![34, 33, -66]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [51, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 70], [0, 1]]
 g := ![![[9, 9], [70, 15], [18, 3], [40], [24], [1]], ![[67, 62], [1, 56], [61, 68], [40], [24], [1]]]
 h' := ![![[38, 70], [51, 3], [5, 21], [22, 43], [28, 18], [20, 38], [0, 1]], ![[0, 1], [23, 68], [22, 50], [23, 28], [2, 53], [44, 33], [38, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [70, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [51, 33, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![649, -805, 1545]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-796, -860, 1545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, 0, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-33, 0, 1]] 
 ![![71, 0, 0], ![19, 1, 0], ![38, 0, 1]] where
  M :=![![![-33, 0, 1], ![0, 2, -1], ![14, -7, 2]]]
  hmulB := by decide  
  f := ![![![-3, -7, -2]], ![![-1, -3, -1]], ![![-2, -7, -2]]]
  g := ![![![-1, 0, 1], ![0, 2, -1], ![1, -7, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-3, -7, -2]] ![![-33, 0, 1]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [3, 37, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 53, 32], [25, 19, 41], [0, 1]]
 g := ![![[63, 19, 46], [71, 3], [47, 27], [13, 1, 25], [55, 1], []], ![[38, 59, 14, 9], [63, 32], [42, 18], [17, 31, 72, 36], [53, 69], [71, 2]], ![[71, 31, 32, 19], [65, 61], [55, 23], [61, 18, 52, 55], [7, 35], [62, 2]]]
 h' := ![![[30, 53, 32], [55, 72, 51], [66, 36, 21], [34, 23, 10], [54, 6, 68], [0, 0, 1], [0, 1]], ![[25, 19, 41], [22, 31, 61], [24, 36, 18], [2, 46, 50], [11, 65, 24], [30, 36, 19], [30, 53, 32]], ![[0, 1], [8, 43, 34], [38, 1, 34], [35, 4, 13], [53, 2, 54], [1, 37, 53], [25, 19, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 39], []]
 b := ![[], [25, 6, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [3, 37, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![539397, 666563, 1337360]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7389, 9131, 18320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [44, 46, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 78, 29], [54, 0, 50], [0, 1]]
 g := ![![[48, 66, 52], [49, 66, 13], [66, 44, 4], [77, 8, 31], [75, 1], []], ![[13, 69, 15, 17], [77, 63, 29, 28], [48, 57, 67, 27], [74, 16, 76, 61], [], [54, 51]], ![[71, 70, 52, 64], [77, 51, 68, 55], [26, 35, 24, 36], [34, 39, 56, 50], [15, 1], [33, 51]]]
 h' := ![![[21, 78, 29], [56, 22, 17], [19, 7, 31], [9, 64, 77], [18, 61, 49], [0, 0, 1], [0, 1]], ![[54, 0, 50], [13, 21, 6], [63, 11, 45], [9, 75, 39], [20, 49, 31], [40, 49], [21, 78, 29]], ![[0, 1], [62, 36, 56], [40, 61, 3], [63, 19, 42], [77, 48, 78], [42, 30, 78], [54, 0, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 16], []]
 b := ![[], [5, 46, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [44, 46, 4, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-537911, -1411730, -1312585]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6809, -17870, -16615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB212I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB212I1 : PrimesBelowBoundCertificateInterval O 31 79 212 where
  m := 11
  g := ![3, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB212I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I41N1, I53N1, I59N1, I61N1, I67N0, I67N1, I71N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N1], [], [], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
