
import IdealArithmetic.Examples.NF3_1_592379_1.RI3_1_592379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-36, -42, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-36, -42, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![103, 97, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-36, -42, 1], ![86, -85, -41], ![-3526, 2095, -126]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -97, 139]], ![![-1, -1, 1], ![31, 28, -41], ![68, 103, -126]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [26, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 138], [0, 1]]
 g := ![![[115, 69], [108, 125], [127], [34, 100], [124], [37], [1]], ![[81, 70], [129, 14], [127], [23, 39], [124], [37], [1]]]
 h' := ![![[68, 138], [111, 114], [32, 60], [89, 108], [37, 10], [131, 92], [113, 68], [0, 1]], ![[0, 1], [79, 25], [81, 79], [66, 31], [22, 129], [132, 47], [11, 71], [68, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [55, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [26, 71, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284, -132, -116]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![88, 80, -116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![41, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![41, 1, 0]] 
 ![![139, 0, 0], ![41, 1, 0], ![126, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![41, 1, 0], ![0, 41, 1], ![86, -49, 42]]]
  hmulB := by decide  
  f := ![![![2215, 54, 0], ![-7506, 0, 0]], ![![615, 15, 0], ![-2084, 0, 0]], ![![1940, 47, 0], ![-6574, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 139, 0], ![-126, 0, 139]], ![![0, 1, 0], ![-13, 41, 1], ![-23, -49, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-36, -42, 1]] ![![139, 0, 0], ![41, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![5699, 139, 0]], ![![-5004, -5838, 139], ![-1390, -1807, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![41, 1, 0]]], ![![![-36, -42, 1]], ![![-10, -13, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![40, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![40, 1, 0]] 
 ![![149, 0, 0], ![40, 1, 0], ![39, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![40, 1, 0], ![0, 40, 1], ![86, -49, 41]]]
  hmulB := by decide  
  f := ![![![1401, 35, 0], ![-5215, 0, 0]], ![![360, 9, 0], ![-1340, 0, 0]], ![![291, 7, 0], ![-1083, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 149, 0], ![-39, 0, 149]], ![![0, 1, 0], ![-11, 40, 1], ![3, -49, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-29, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-29, 1, 0]] 
 ![![149, 0, 0], ![120, 1, 0], ![53, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-29, 1, 0], ![0, -29, 1], ![86, -49, -28]]]
  hmulB := by decide  
  f := ![![![1393, -48, 0], ![7152, 0, 0]], ![![1132, -39, 0], ![5812, 0, 0]], ![![499, -17, 0], ![2562, 1, 0]]]
  g := ![![![1, 0, 0], ![-120, 149, 0], ![-53, 0, 149]], ![![-1, 1, 0], ![23, -29, 1], ![50, -49, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-12, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-12, 1, 0]] 
 ![![149, 0, 0], ![137, 1, 0], ![5, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-12, 1, 0], ![0, -12, 1], ![86, -49, -11]]]
  hmulB := by decide  
  f := ![![![1117, -93, 0], ![13857, 0, 0]], ![![1033, -86, 0], ![12815, 0, 0]], ![![61, -5, 0], ![757, 1, 0]]]
  g := ![![![1, 0, 0], ![-137, 149, 0], ![-5, 0, 149]], ![![-1, 1, 0], ![11, -12, 1], ![46, -49, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![40, 1, 0]] ![![149, 0, 0], ![-29, 1, 0]]
  ![![149, 0, 0], ![32, 11, 1]] where
 M := ![![![22201, 0, 0], ![-4321, 149, 0]], ![![5960, 149, 0], ![-1160, 11, 1]]]
 hmul := by decide  
 g := ![![![![117, -11, -1], ![149, 0, 0]], ![![-29, 1, 0], ![0, 0, 0]]], ![![![8, -10, -1], ![149, 0, 0]], ![![-8, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![32, 11, 1]] ![![149, 0, 0], ![-12, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-1788, 149, 0]], ![![4768, 1639, 149], ![-298, -149, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-12, 1, 0]]], ![![![32, 11, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [150, 54, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 33, 11], [108, 117, 140], [0, 1]]
 g := ![![[49, 145, 110], [32, 131, 2], [8, 54, 95], [69, 47], [137, 133, 22], [6, 1], []], ![[70, 54, 32, 62], [22, 24, 27, 80], [135, 66, 11, 148], [58, 99], [106, 17, 71, 97], [96, 99], [93, 121]], ![[100, 63, 2, 24], [128, 9, 22, 132], [52, 115, 11, 27], [3, 43], [140, 77, 81, 141], [135, 32], [115, 121]]]
 h' := ![![[49, 33, 11], [32, 128, 67], [8, 85, 46], [114, 17, 47], [137, 19, 54], [6, 130, 133], [0, 0, 1], [0, 1]], ![[108, 117, 140], [54, 47, 36], [60, 113, 126], [83, 128, 99], [146, 1, 34], [140, 19, 79], [78, 145, 117], [49, 33, 11]], ![[0, 1], [31, 127, 48], [23, 104, 130], [34, 6, 5], [129, 131, 63], [136, 2, 90], [1, 6, 33], [108, 117, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 55], []]
 b := ![[], [68, 30, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [150, 54, 145, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163382, -95583, 1208]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1082, -633, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![98, -61, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![98, -61, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![98, 96, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![98, -61, 1], ![86, 49, -60], ![-5160, 3026, -11]]]
  hmulB := by decide  
  f := ![![![-97, 61, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -96, 157]], ![![0, -1, 1], ![38, 37, -60], ![-26, 26, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [139, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 156], [0, 1]]
 g := ![![[97, 127], [110], [35, 138], [142, 46], [41, 49], [47], [1]], ![[155, 30], [110], [145, 19], [74, 111], [30, 108], [47], [1]]]
 h' := ![![[19, 156], [100, 136], [2, 61], [44, 83], [110, 108], [71, 7], [18, 19], [0, 1]], ![[0, 1], [15, 21], [62, 96], [51, 74], [121, 49], [47, 150], [65, 138], [19, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [78, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [139, 138, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4683, 145, -59]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 37, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![60, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![60, 1, 0]] 
 ![![157, 0, 0], ![60, 1, 0], ![11, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![60, 1, 0], ![0, 60, 1], ![86, -49, 61]]]
  hmulB := by decide  
  f := ![![![3421, 57, 0], ![-8949, 0, 0]], ![![1260, 21, 0], ![-3296, 0, 0]], ![![203, 3, 0], ![-531, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 157, 0], ![-11, 0, 157]], ![![0, 1, 0], ![-23, 60, 1], ![15, -49, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![98, -61, 1]] ![![157, 0, 0], ![60, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![9420, 157, 0]], ![![15386, -9577, 157], ![5966, -3611, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![60, 1, 0]]], ![![![98, -61, 1]], ![![38, -23, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![56, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![56, 1, 0]] 
 ![![163, 0, 0], ![56, 1, 0], ![124, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![56, 1, 0], ![0, 56, 1], ![86, -49, 57]]]
  hmulB := by decide  
  f := ![![![3641, 65, 0], ![-10595, 0, 0]], ![![1176, 21, 0], ![-3422, 0, 0]], ![![2820, 50, 0], ![-8206, 1, 0]]]
  g := ![![![1, 0, 0], ![-56, 163, 0], ![-124, 0, 163]], ![![0, 1, 0], ![-20, 56, 1], ![-26, -49, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-47, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-47, 1, 0]] 
 ![![163, 0, 0], ![116, 1, 0], ![73, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-47, 1, 0], ![0, -47, 1], ![86, -49, -46]]]
  hmulB := by decide  
  f := ![![![6158, -131, 0], ![21353, 0, 0]], ![![4372, -93, 0], ![15160, 0, 0]], ![![2740, -58, 0], ![9501, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 163, 0], ![-73, 0, 163]], ![![-1, 1, 0], ![33, -47, 1], ![56, -49, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-10, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-10, 1, 0]] 
 ![![163, 0, 0], ![153, 1, 0], ![63, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-10, 1, 0], ![0, -10, 1], ![86, -49, -9]]]
  hmulB := by decide  
  f := ![![![551, -55, 0], ![8965, 0, 0]], ![![501, -50, 0], ![8151, 0, 0]], ![![211, -21, 0], ![3433, 1, 0]]]
  g := ![![![1, 0, 0], ![-153, 163, 0], ![-63, 0, 163]], ![![-1, 1, 0], ![9, -10, 1], ![50, -49, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![56, 1, 0]] ![![163, 0, 0], ![-47, 1, 0]]
  ![![163, 0, 0], ![-24, 9, 1]] where
 M := ![![![26569, 0, 0], ![-7661, 163, 0]], ![![9128, 163, 0], ![-2632, 9, 1]]]
 hmul := by decide  
 g := ![![![![163, 0, 0], ![0, 0, 0]], ![![-23, -8, -1], ![163, 0, 0]]], ![![![56, 1, 0], ![0, 0, 0]], ![![8, -9, -1], ![164, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-24, 9, 1]] ![![163, 0, 0], ![-10, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-1630, 163, 0]], ![![-3912, 1467, 163], ![326, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-10, 1, 0]]], ![![![-24, 9, 1]], ![![2, -1, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 4, -2]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-1, 4, -2]] 
 ![![167, 0, 0], ![76, 1, 0], ![69, 0, 1]] where
  M :=![![![-1, 4, -2], ![-172, 97, 2], ![172, -270, 99]]]
  hmulB := by decide  
  f := ![![![-10143, -144, -202]], ![![-4720, -67, -94]], ![![-4369, -62, -87]]]
  g := ![![![-1, 4, -2], ![-46, 97, 2], ![83, -270, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-48, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-48, 1, 0]] 
 ![![167, 0, 0], ![119, 1, 0], ![34, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-48, 1, 0], ![0, -48, 1], ![86, -49, -47]]]
  hmulB := by decide  
  f := ![![![5329, -111, 0], ![18537, 0, 0]], ![![3745, -78, 0], ![13027, 0, 0]], ![![1070, -22, 0], ![3722, 1, 0]]]
  g := ![![![1, 0, 0], ![-119, 167, 0], ![-34, 0, 167]], ![![-1, 1, 0], ![34, -48, 1], ![45, -49, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-29, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-29, 1, 0]] 
 ![![167, 0, 0], ![138, 1, 0], ![161, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-29, 1, 0], ![0, -29, 1], ![86, -49, -28]]]
  hmulB := by decide  
  f := ![![![4409, -152, 0], ![25384, 0, 0]], ![![3626, -125, 0], ![20876, 0, 0]], ![![4269, -147, 0], ![24578, 1, 0]]]
  g := ![![![1, 0, 0], ![-138, 167, 0], ![-161, 0, 167]], ![![-1, 1, 0], ![23, -29, 1], ![68, -49, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-1, 4, -2]] ![![167, 0, 0], ![-48, 1, 0]]
  ![![167, 0, 0], ![26, 28, 1]] where
 M := ![![![-167, 668, -334], ![-124, -95, 98]]]
 hmul := by decide  
 g := ![![![![-27, -24, -3], ![167, 0, 0]], ![![-16, -17, 0], ![98, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![26, 28, 1]] ![![167, 0, 0], ![-29, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-4843, 167, 0]], ![![4342, 4676, 167], ![-668, -835, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-29, 1, 0]]], ![![![26, 28, 1]], ![![-4, -5, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![28, -35, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![28, -35, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![28, 138, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![28, -35, 1], ![86, -21, -34], ![-2924, 1752, -55]]]
  hmulB := by decide  
  f := ![![![-27, 35, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -138, 173]], ![![0, -1, 1], ![6, 27, -34], ![-8, 54, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [154, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 172], [0, 1]]
 g := ![![[45, 150], [172], [48, 4], [74, 23], [92], [4, 100], [1]], ![[102, 23], [172], [8, 169], [17, 150], [92], [42, 73], [1]]]
 h' := ![![[163, 172], [114, 91], [47, 80], [22, 2], [85, 14], [76, 145], [19, 163], [0, 1]], ![[0, 1], [69, 82], [112, 93], [2, 171], [118, 159], [10, 28], [119, 10], [163, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [112, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [154, 10, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![423, 639, -473]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79, 381, -473]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![34, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![34, 1, 0]] 
 ![![173, 0, 0], ![34, 1, 0], ![55, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![34, 1, 0], ![0, 34, 1], ![86, -49, 35]]]
  hmulB := by decide  
  f := ![![![1633, 48, 0], ![-8304, 0, 0]], ![![306, 9, 0], ![-1556, 0, 0]], ![![483, 14, 0], ![-2456, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 173, 0], ![-55, 0, 173]], ![![0, 1, 0], ![-7, 34, 1], ![-1, -49, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![28, -35, 1]] ![![173, 0, 0], ![34, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![5882, 173, 0]], ![![4844, -6055, 173], ![1038, -1211, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![34, 1, 0]]], ![![![28, -35, 1]], ![![6, -7, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 21, -2]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-29, 21, -2]] 
 ![![179, 0, 0], ![0, 179, 0], ![104, 79, 1]] where
  M :=![![![-29, 21, -2], ![-172, 69, 19], ![1634, -1103, 88]]]
  hmulB := by decide  
  f := ![![![151, 2, 3]], ![![258, 4, 5]], ![![204, 3, 4]]]
  g := ![![![1, 1, -2], ![-12, -8, 19], ![-42, -45, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [19, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 178], [0, 1]]
 g := ![![[59, 66], [39, 77], [25], [76], [166, 149], [172, 61], [1]], ![[0, 113], [0, 102], [25], [76], [144, 30], [169, 118], [1]]]
 h' := ![![[132, 178], [154, 148], [36, 16], [137, 5], [68, 75], [133, 68], [160, 132], [0, 1]], ![[0, 1], [0, 31], [0, 163], [81, 174], [123, 104], [159, 111], [42, 47], [132, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [27, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [19, 47, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![277, -108, -92]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 40, -92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -2, -3]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-151, -2, -3]] 
 ![![179, 0, 0], ![99, 1, 0], ![44, 0, 1]] where
  M :=![![![-151, -2, -3], ![-258, -4, -5], ![-430, -13, -9]]]
  hmulB := by decide  
  f := ![![![29, -21, 2]], ![![17, -12, 1]], ![![-2, 1, 0]]]
  g := ![![![1, -2, -3], ![2, -4, -5], ![7, -13, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-29, 21, -2]] ![![-151, -2, -3]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![4, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![4, 1, 0]] 
 ![![181, 0, 0], ![4, 1, 0], ![165, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![4, 1, 0], ![0, 4, 1], ![86, -49, 5]]]
  hmulB := by decide  
  f := ![![![521, 130, 0], ![-23530, 0, 0]], ![![4, 1, 0], ![-180, 0, 0]], ![![473, 118, 0], ![-21362, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 181, 0], ![-165, 0, 181]], ![![0, 1, 0], ![-1, 4, 1], ![-3, -49, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![49, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![49, 1, 0]] 
 ![![181, 0, 0], ![49, 1, 0], ![133, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![49, 1, 0], ![0, 49, 1], ![86, -49, 50]]]
  hmulB := by decide  
  f := ![![![4068, 83, 0], ![-15023, 0, 0]], ![![1078, 22, 0], ![-3981, 0, 0]], ![![2954, 60, 0], ![-10909, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 181, 0], ![-133, 0, 181]], ![![0, 1, 0], ![-14, 49, 1], ![-23, -49, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-54, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-54, 1, 0]] 
 ![![181, 0, 0], ![127, 1, 0], ![161, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-54, 1, 0], ![0, -54, 1], ![86, -49, -53]]]
  hmulB := by decide  
  f := ![![![4267, -79, 0], ![14299, 0, 0]], ![![3025, -56, 0], ![10137, 0, 0]], ![![3851, -71, 0], ![12905, 1, 0]]]
  g := ![![![1, 0, 0], ![-127, 181, 0], ![-161, 0, 181]], ![![-1, 1, 0], ![37, -54, 1], ![82, -49, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![4, 1, 0]] ![![181, 0, 0], ![49, 1, 0]]
  ![![181, 0, 0], ![15, 53, 1]] where
 M := ![![![32761, 0, 0], ![8869, 181, 0]], ![![724, 181, 0], ![196, 53, 1]]]
 hmul := by decide  
 g := ![![![![166, -53, -1], ![181, 0, 0]], ![![34, -52, -1], ![181, 0, 0]]], ![![![-11, -52, -1], ![181, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![15, 53, 1]] ![![181, 0, 0], ![-54, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-9774, 181, 0]], ![![2715, 9593, 181], ![-724, -2896, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-54, 1, 0]]], ![![![15, 53, 1]], ![![-4, -16, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![9, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![9, 1, 0]] 
 ![![191, 0, 0], ![9, 1, 0], ![110, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![9, 1, 0], ![0, 9, 1], ![86, -49, 10]]]
  hmulB := by decide  
  f := ![![![730, 81, 0], ![-15471, 0, 0]], ![![18, 2, 0], ![-381, 0, 0]], ![![406, 45, 0], ![-8604, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 191, 0], ![-110, 0, 191]], ![![0, 1, 0], ![-1, 9, 1], ![-3, -49, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, 1]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-3, 0, 1]] 
 ![![191, 0, 0], ![24, 1, 0], ![188, 0, 1]] where
  M :=![![![-3, 0, 1], ![86, -52, 1], ![86, 37, -51]]]
  hmulB := by decide  
  f := ![![![-2615, -37, -52]], ![![-352, -5, -7]], ![![-2614, -37, -52]]]
  g := ![![![-1, 0, 1], ![6, -52, 1], ![46, 37, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-34, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-34, 1, 0]] 
 ![![191, 0, 0], ![157, 1, 0], ![181, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-34, 1, 0], ![0, -34, 1], ![86, -49, -33]]]
  hmulB := by decide  
  f := ![![![4557, -134, 0], ![25594, 0, 0]], ![![3775, -111, 0], ![21202, 0, 0]], ![![4359, -128, 0], ![24482, 1, 0]]]
  g := ![![![1, 0, 0], ![-157, 191, 0], ![-181, 0, 191]], ![![-1, 1, 0], ![27, -34, 1], ![72, -49, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![9, 1, 0]] ![![-3, 0, 1]]
  ![![191, 0, 0], ![25, 33, 1]] where
 M := ![![![-573, 0, 191]], ![![59, -52, 10]]]
 hmul := by decide  
 g := ![![![![-3, 0, 1], ![0, 0, 0]]], ![![![-1, -2, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![25, 33, 1]] ![![191, 0, 0], ![-34, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-6494, 191, 0]], ![![4775, 6303, 191], ![-764, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-34, 1, 0]]], ![![![25, 33, 1]], ![![-4, -6, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [77, 161, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [174, 148, 175], [137, 44, 18], [0, 1]]
 g := ![![[98, 46, 83], [19, 54], [22, 169], [11, 28], [81, 150], [48, 28], [1]], ![[148, 30, 90, 3], [108, 2], [40, 93], [93, 25], [99, 31], [98, 63], [192, 16, 133, 151]], ![[120, 96, 5, 86], [172, 81], [127, 46], [123, 31], [102, 107], [26, 175], [80, 3, 53, 42]]]
 h' := ![![[174, 148, 175], [174, 89, 58], [155, 41, 132], [43, 184, 13], [73, 85, 118], [110, 49, 27], [116, 32, 118], [0, 1]], ![[137, 44, 18], [92, 148, 178], [63, 73, 52], [172, 88, 155], [81, 112, 188], [131, 91, 113], [166, 181, 177], [174, 148, 175]], ![[0, 1], [75, 149, 150], [52, 79, 9], [48, 114, 25], [107, 189, 80], [56, 53, 53], [30, 173, 91], [137, 44, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 165], []]
 b := ![[], [77, 93, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [77, 161, 75, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![708696, -297027, -15633]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3672, -1539, -81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB218I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB218I3 : PrimesBelowBoundCertificateInterval O 137 193 218 where
  m := 11
  g := ![2, 3, 1, 2, 3, 3, 2, 2, 3, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB218I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![191, 191, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N0, I149N1, I149N2, I157N1, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N1, I179N1, I181N0, I181N1, I181N2, I191N0, I191N1, I191N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [I157N1], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
