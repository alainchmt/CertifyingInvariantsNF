
import IdealArithmetic.Examples.NF3_1_117175_1.RI3_1_117175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12647, 5409, 1451]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-12647, 5409, 1451]] 
 ![![37, 0, 0], ![9, 1, 0], ![30, 0, 1]] where
  M :=![![![-12647, 5409, 1451], ![65295, -48922, 5409], ![243405, -69930, -48922]]]
  hmulB := by decide  
  f := ![![![2771613454, 163150668, 100243103]], ![![796093533, 46861943, 28792935]], ![![2445680640, 143964675, 88454837]]]
  g := ![![![-2834, 5409, 1451], ![9279, -48922, 5409], ![63255, -69930, -48922]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 5, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![83, 5, 3]] 
 ![![37, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![83, 5, 3], ![135, 8, 5], ![225, 10, 8]]]
  hmulB := by decide  
  f := ![![![14, -10, 1]], ![![5, -3, 0]], ![![-8, 5, 0]]]
  g := ![![![0, 5, 3], ![0, 8, 5], ![1, 10, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27972218, 1646581, 1011693]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![27972218, 1646581, 1011693]] 
 ![![37, 0, 0], ![18, 1, 0], ![9, 0, 1]] where
  M :=![![![27972218, 1646581, 1011693], ![45526185, 2679893, 1646581], ![74096145, 4361660, 2679893]]]
  hmulB := by decide  
  f := ![![![6989, -5453, 712]], ![![4266, -2945, 199]], ![![-4932, 3224, -119]]]
  g := ![![![-291121, 1646581, 1011693], ![-473814, 2679893, 1646581], ![-771156, 4361660, 2679893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-12647, 5409, 1451]] ![![83, 5, 3]]
  ![![6989, -5453, 712]] where
 M := ![![![6989, -5453, 712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![6989, -5453, 712]] ![![27972218, 1646581, 1011693]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17696276, 1041689, 640035]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![17696276, 1041689, 640035]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 5, 1]] where
  M :=![![![17696276, 1041689, 640035], ![28801575, 1695401, 1041689], ![46876005, 2759350, 1695401]]]
  hmulB := by decide  
  f := ![![![211, 121, -154]], ![![-6930, 4061, 121]], ![![-666, 279, 80]]]
  g := ![![![291121, -52646, 640035], ![473814, -85684, 1041689], ![771156, -139455, 1695401]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [4, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[21, 31], [31], [10], [8, 4], [1]], ![[0, 10], [31], [10], [0, 37], [1]]]
 h' := ![![[39, 40], [40, 20], [0, 20], [9, 25], [37, 39], [0, 1]], ![[0, 1], [0, 21], [1, 21], [0, 16], [0, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [4, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![94, -7, -26]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 3, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 121, -154]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![211, 121, -154]] 
 ![![41, 0, 0], ![36, 1, 0], ![16, 0, 1]] where
  M :=![![![211, 121, -154], ![-6930, 4061, 121], ![5445, -9955, 4061]]]
  hmulB := by decide  
  f := ![![![17696276, 1041689, 640035]], ![![16240671, 956005, 587389]], ![![8049181, 473814, 291121]]]
  g := ![![![-41, 121, -154], ![-3782, 4061, 121], ![7289, -9955, 4061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![17696276, 1041689, 640035]] ![![211, 121, -154]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86707, -5104, -3136]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-86707, -5104, -3136]] 
 ![![43, 0, 0], ![14, 1, 0], ![19, 0, 1]] where
  M :=![![![-86707, -5104, -3136], ![-141120, -8307, -5104], ![-229680, -13520, -8307]]]
  hmulB := by decide  
  f := ![![![-169, 208, -64]], ![![-122, 101, -16]], ![![143, -96, 5]]]
  g := ![![![1031, -5104, -3136], ![1678, -8307, -5104], ![2731, -13520, -8307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 8, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-13, 8, 0]] 
 ![![43, 0, 0], ![36, 1, 0], ![37, 0, 1]] where
  M :=![![![-13, 8, 0], ![0, -13, 8], ![360, -200, -13]]]
  hmulB := by decide  
  f := ![![![1769, 104, 64]], ![![1548, 91, 56]], ![![1631, 96, 59]]]
  g := ![![![-7, 8, 0], ![4, -13, 8], ![187, -200, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-86707, -5104, -3136]] ![![-13, 8, 0]]
  ![![-1769, -104, -64]] where
 M := ![![![-1769, -104, -64]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-1769, -104, -64]] ![![-13, 8, 0]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6512976169, -383385501, -235559883]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-6512976169, -383385501, -235559883]] 
 ![![47, 0, 0], ![0, 47, 0], ![10, 28, 1]] where
  M :=![![![-6512976169, -383385501, -235559883], ![-10600194735, -623979094, -383385501], ![-17252347545, -1015557210, -623979094]]]
  hmulB := by decide  
  f := ![![![20242, -14688, 1383]], ![![62235, -14333, -14688]], ![![27320, -2527, -8761]]]
  g := ![![![-88454837, 132176409, -235559883], ![-143964675, 215123722, -383385501], ![-234309715, 350124626, -623979094]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [38, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[10, 8], [39, 32], [45, 7], [5, 16], [1]], ![[25, 39], [5, 15], [17, 40], [35, 31], [1]]]
 h' := ![![[43, 46], [22, 33], [29, 28], [45, 17], [9, 43], [0, 1]], ![[0, 1], [31, 14], [11, 19], [24, 30], [25, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [18, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [38, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-505, 701, -215]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 143, -215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20242, 14688, -1383]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-20242, 14688, -1383]] 
 ![![47, 0, 0], ![19, 1, 0], ![15, 0, 1]] where
  M :=![![![-20242, 14688, -1383], ![-62235, 14333, 14688], ![660960, -429435, 14333]]]
  hmulB := by decide  
  f := ![![![6512976169, 383385501, 235559883]], ![![2858441318, 168261779, 103383474]], ![![2445680640, 143964675, 88454837]]]
  g := ![![![-5927, 14688, -1383], ![-11806, 14333, 14688], ![183090, -429435, 14333]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-6512976169, -383385501, -235559883]] ![![-20242, 14688, -1383]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44212889, 2602586, 1599082]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![44212889, 2602586, 1599082]] 
 ![![53, 0, 0], ![0, 53, 0], ![18, 29, 1]] where
  M :=![![![44212889, 2602586, 1599082], ![71958690, 4235839, 2602586], ![117116370, 6894040, 4235839]]]
  hmulB := by decide  
  f := ![![![877, -158, -234]], ![![-10530, 6727, -158]], ![![-5598, 3503, -39]]]
  g := ![![![291121, -825864, 1599082], ![473814, -1344135, 2602586], ![771156, -2187647, 4235839]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [36, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 52], [0, 1]]
 g := ![![[12, 28], [42], [31, 4], [42], [45, 1]], ![[0, 25], [42], [52, 49], [42], [37, 52]]]
 h' := ![![[45, 52], [34, 44], [50, 25], [24, 51], [23, 28], [0, 1]], ![[0, 1], [0, 9], [9, 28], [40, 2], [11, 25], [45, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [16, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [36, 8, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3530, -25, 96]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34, -53, 96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-877, 158, 234]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-877, 158, 234]] 
 ![![53, 0, 0], ![24, 1, 0], ![7, 0, 1]] where
  M :=![![![-877, 158, 234], ![10530, -6727, 158], ![7110, 6580, -6727]]]
  hmulB := by decide  
  f := ![![![-44212889, -2602586, -1599082]], ![![-21378642, -1258451, -773218]], ![![-8049181, -473814, -291121]]]
  g := ![![![-119, 158, 234], ![3224, -6727, 158], ![-1957, 6580, -6727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![44212889, 2602586, 1599082]] ![![-877, 158, 234]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12958136, -762779, -468667]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-12958136, -762779, -468667]] 
 ![![59, 0, 0], ![0, 59, 0], ![50, 54, 1]] where
  M :=![![![-12958136, -762779, -468667], ![-21090015, -1241461, -762779], ![-34325055, -2020540, -1241461]]]
  hmulB := by decide  
  f := ![![![1121, -679, -6]], ![![-270, 1271, -679]], ![![185, 871, -605]]]
  g := ![![![177546, 416021, -468667], ![288965, 677095, -762779], ![470305, 1102006, -1241461]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [24, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 58], [0, 1]]
 g := ![![[10, 29], [53, 25], [46], [37, 5], [55, 1]], ![[12, 30], [12, 34], [46], [17, 54], [51, 58]]]
 h' := ![![[55, 58], [26, 41], [26, 54], [56, 39], [37, 51], [0, 1]], ![[0, 1], [39, 18], [46, 5], [18, 20], [10, 8], [55, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [24, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-241, 561, -242]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![201, 231, -242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1121, -679, -6]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![1121, -679, -6]] 
 ![![59, 0, 0], ![5, 1, 0], ![34, 0, 1]] where
  M :=![![![1121, -679, -6], ![-270, 1271, -679], ![-30555, 16705, 1271]]]
  hmulB := by decide  
  f := ![![![-12958136, -762779, -468667]], ![![-1455605, -85684, -52646]], ![![-8049181, -473814, -291121]]]
  g := ![![![80, -679, -6], ![279, 1271, -679], ![-2666, 16705, 1271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-12958136, -762779, -468667]] ![![1121, -679, -6]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![971, -691, 58]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![971, -691, 58]] 
 ![![61, 0, 0], ![0, 61, 0], ![22, 27, 1]] where
  M :=![![![971, -691, 58], ![2610, -479, -691], ![-31095, 19885, -479]]]
  hmulB := by decide  
  f := ![![![229016, 13481, 8283]], ![![372735, 21941, 13481]], ![![257522, 15159, 9314]]]
  g := ![![![-5, -37, 58], ![292, 298, -691], ![-337, 538, -479]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [34, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 60], [0, 1]]
 g := ![![[5, 9], [27], [13, 15], [38, 47], [13, 1]], ![[0, 52], [27], [25, 46], [39, 14], [26, 60]]]
 h' := ![![[13, 60], [39, 58], [46, 24], [50, 36], [46, 13], [0, 1]], ![[0, 1], [0, 3], [53, 37], [30, 25], [32, 48], [13, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [54, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [34, 48, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124, -53, -72]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 31, -72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229016, 13481, 8283]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![229016, 13481, 8283]] 
 ![![61, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![229016, 13481, 8283], ![372735, 21941, 13481], ![606645, 35710, 21941]]]
  hmulB := by decide  
  f := ![![![971, -691, 58]], ![![584, -393, 21]], ![![-462, 292, -5]]]
  g := ![![![-4167, 13481, 8283], ![-6782, 21941, 13481], ![-11038, 35710, 21941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![971, -691, 58]] ![![229016, 13481, 8283]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24751, -23093, 4845]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![24751, -23093, 4845]] 
 ![![67, 0, 0], ![0, 67, 0], ![46, 17, 1]] where
  M :=![![![24751, -23093, 4845], ![218025, -96374, -23093], ![-1039185, 795350, -96374]]]
  hmulB := by decide  
  f := ![![![-412760678, -24297104, -14928637]], ![![-671788665, -39544753, -24297104]], ![![-470160719, -27675950, -17004669]]]
  g := ![![![-2957, -1574, 4845], ![19109, 4421, -23093], ![50657, 36324, -96374]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [54, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 66], [0, 1]]
 g := ![![[42, 36], [51, 15], [54], [35], [33], [1]], ![[0, 31], [0, 52], [54], [35], [33], [1]]]
 h' := ![![[10, 66], [60, 61], [19, 45], [11, 11], [62, 54], [13, 10], [0, 1]], ![[0, 1], [0, 6], [0, 22], [54, 56], [66, 13], [46, 57], [10, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [8, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [54, 57, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1822, 216, 395]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-244, -97, 395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-412760678, -24297104, -14928637]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-412760678, -24297104, -14928637]] 
 ![![67, 0, 0], ![50, 1, 0], ![46, 0, 1]] where
  M :=![![![-412760678, -24297104, -14928637], ![-671788665, -39544753, -24297104], ![-1093369680, -64361065, -39544753]]]
  hmulB := by decide  
  f := ![![![24751, -23093, 4845]], ![![21725, -18672, 3271]], ![![1483, -3984, 1888]]]
  g := ![![![22221072, -24297104, -14928637], ![36165907, -39544753, -24297104], ![58861824, -64361065, -39544753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![24751, -23093, 4845]] ![![-412760678, -24297104, -14928637]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, -1, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![26, -1, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![26, 70, 1]] where
  M :=![![![26, -1, 1], ![45, 1, -1], ![-45, 70, 1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0]], ![![0, 1, 1]], ![![1, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 1, -1], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [69, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 70], [0, 1]]
 g := ![![[26, 15], [58, 36], [25, 54], [32], [6], [1]], ![[25, 56], [13, 35], [64, 17], [32], [6], [1]]]
 h' := ![![[52, 70], [45, 50], [50, 6], [36, 57], [16, 23], [2, 52], [0, 1]], ![[0, 1], [18, 21], [7, 65], [18, 14], [5, 48], [8, 19], [52, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [24, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [69, 19, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219, 246, -33]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 36, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![71, 0, 0], ![1, 1, 0], ![70, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![45, -25, 1]]]
  hmulB := by decide  
  f := ![![![26, -1, 1]], ![![1, 0, 0]], ![![25, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, -25, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![26, -1, 1]] ![![1, 1, 0]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-405029, -23842, -14649]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-405029, -23842, -14649]] 
 ![![73, 0, 0], ![0, 73, 0], ![2, 59, 1]] where
  M :=![![![-405029, -23842, -14649], ![-659205, -38804, -23842], ![-1072890, -63155, -38804]]]
  hmulB := by decide  
  f := ![![![-122, 101, -16]], ![![-720, 278, 101]], ![![-523, 183, 85]]]
  g := ![![![-5147, 11513, -14649], ![-8377, 18738, -23842], ![-13634, 30497, -38804]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [1, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 72], [0, 1]]
 g := ![![[40, 1], [48], [46], [57, 54], [67], [1]], ![[0, 72], [48], [46], [14, 19], [67], [1]]]
 h' := ![![[33, 72], [33, 72], [64, 11], [16, 51], [7, 28], [72, 33], [0, 1]], ![[0, 1], [0, 1], [62, 62], [20, 22], [55, 45], [66, 40], [33, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [4, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [1, 40, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![181, 120, -19]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 17, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-122, 101, -16]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-122, 101, -16]] 
 ![![73, 0, 0], ![14, 1, 0], ![23, 0, 1]] where
  M :=![![![-122, 101, -16], ![-720, 278, 101], ![4545, -3245, 278]]]
  hmulB := by decide  
  f := ![![![-405029, -23842, -14649]], ![![-86707, -5104, -3136]], ![![-142309, -8377, -5147]]]
  g := ![![![-16, 101, -16], ![-95, 278, 101], ![597, -3245, 278]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-405029, -23842, -14649]] ![![-122, 101, -16]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2121203431, 124864366, 76719217]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![2121203431, 124864366, 76719217]] 
 ![![79, 0, 0], ![0, 79, 0], ![77, 17, 1]] where
  M :=![![![2121203431, 124864366, 76719217], ![3452364765, 203223006, 124864366], ![5618896470, 330755615, 203223006]]]
  hmulB := by decide  
  f := ![![![-3026, 4421, -1574]], ![![-70830, 36324, 4421]], ![![-15673, 9830, -123]]]
  g := ![![![-47926282, -14928637, 76719217], ![-78002423, -24297104, 124864366], ![-126952848, -39544753, 203223006]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [20, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 78], [0, 1]]
 g := ![![[41, 4], [3, 8], [52, 52], [52, 62], [31], [1]], ![[0, 75], [0, 71], [72, 27], [9, 17], [31], [1]]]
 h' := ![![[49, 78], [19, 77], [66, 18], [66, 17], [17, 33], [59, 49], [0, 1]], ![[0, 1], [0, 2], [0, 61], [30, 62], [54, 46], [11, 30], [49, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [78, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [20, 30, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1716, 840, 68]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88, -4, 68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3026, 4421, -1574]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-3026, 4421, -1574]] 
 ![![79, 0, 0], ![62, 1, 0], ![27, 0, 1]] where
  M :=![![![-3026, 4421, -1574], ![-70830, 36324, 4421], ![198945, -181355, 36324]]]
  hmulB := by decide  
  f := ![![![2121203431, 124864366, 76719217]], ![![1708442753, 100567262, 61790580]], ![![796093533, 46861943, 28792935]]]
  g := ![![![-2970, 4421, -1574], ![-30915, 36324, 4421], ![132433, -181355, 36324]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![2121203431, 124864366, 76719217]] ![![-3026, 4421, -1574]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB97I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB97I1 : PrimesBelowBoundCertificateInterval O 31 79 97 where
  m := 11
  g := ![3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB97I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I43N1, I47N1, I53N1, I59N1, I61N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N1], [I47N1], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
