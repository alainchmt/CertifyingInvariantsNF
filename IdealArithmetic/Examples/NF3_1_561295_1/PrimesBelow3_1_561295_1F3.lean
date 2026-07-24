
import IdealArithmetic.Examples.NF3_1_561295_1.RI3_1_561295_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![52, -53, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![52, -53, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![52, 86, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![52, -53, 1], ![-132, 188, -473], ![4123, 1200, -180]]]
  hmulB := by decide  
  f := ![![![-51, 53, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -86, 139]], ![![0, -1, 1], ![176, 294, -473], ![97, 120, -180]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [118, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 138], [0, 1]]
 g := ![![[79, 86], [66, 100], [64], [82, 41], [25], [81], [1]], ![[0, 53], [0, 39], [64], [130, 98], [25], [81], [1]]]
 h' := ![![[130, 138], [135, 15], [90, 10], [54, 8], [21, 67], [57, 5], [21, 130], [0, 1]], ![[0, 1], [0, 124], [0, 129], [121, 131], [113, 72], [12, 134], [102, 9], [130, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [5, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [118, 9, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2226, -709, -1791]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![654, 1103, -1791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![56, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![56, 1, 0]] 
 ![![139, 0, 0], ![56, 1, 0], ![41, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![56, 1, 0], ![1, 53, 9], ![-79, -23, 60]]]
  hmulB := by decide  
  f := ![![![-1191, -83945, -14256], ![-973, 220176, 0]], ![![-470, -33811, -5742], ![-416, 88682, 0]], ![![-365, -24761, -4205], ![-253, 64944, 0]]]
  g := ![![![1, 0, 0], ![-56, 139, 0], ![-41, 0, 139]], ![![0, 1, 0], ![-24, 53, 9], ![-9, -23, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![52, -53, 1]] ![![139, 0, 0], ![56, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![7784, 139, 0]], ![![7228, -7367, 139], ![2780, -2780, -417]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![56, 1, 0]]], ![![![52, -53, 1]], ![![20, -20, -3]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-48, 40, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-48, 40, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![101, 40, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-48, 40, 1], ![-39, -191, 364], ![-3224, -939, 92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -40, 149]], ![![-1, 0, 1], ![-247, -99, 364], ![-84, -31, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [30, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 148], [0, 1]]
 g := ![![[46, 5], [69], [41, 33], [16], [91, 145], [31], [1]], ![[0, 144], [69], [95, 116], [16], [98, 4], [31], [1]]]
 h' := ![![[110, 148], [119, 68], [111, 48], [36, 35], [101, 4], [119, 88], [119, 110], [0, 1]], ![[0, 1], [0, 81], [27, 101], [12, 114], [94, 145], [114, 61], [1, 39], [110, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [126, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [30, 39, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4107, 377, -7042]
  a := ![2, -9, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4801, 1893, -7042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-66, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-66, 1, 0]] 
 ![![149, 0, 0], ![83, 1, 0], ![57, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-66, 1, 0], ![1, -69, 9], ![-79, -23, -62]]]
  hmulB := by decide  
  f := ![![![-7731, 806688, -105228], ![8940, 1742108, 0]], ![![-4267, 449294, -58608], ![5067, 970288, 0]], ![![-2907, 308598, -40255], ![3534, 666444, 0]]]
  g := ![![![1, 0, 0], ![-83, 149, 0], ![-57, 0, 149]], ![![-1, 1, 0], ![35, -69, 9], ![36, -23, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-48, 40, 1]] ![![149, 0, 0], ![-66, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9834, 149, 0]], ![![-7152, 5960, 149], ![3129, -2831, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-66, 1, 0]]], ![![![-48, 40, 1]], ![![21, -19, 2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![25, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![25, 1, 0]] 
 ![![151, 0, 0], ![25, 1, 0], ![90, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![25, 1, 0], ![1, 22, 9], ![-79, -23, 29]]]
  hmulB := by decide  
  f := ![![![-17079, -395524, -161820], ![-5436, 2714980, 0]], ![![-2851, -65467, -26784], ![-754, 449376, 0]], ![![-10185, -235743, -96449], ![-3207, 1618200, 0]]]
  g := ![![![1, 0, 0], ![-25, 151, 0], ![-90, 0, 151]], ![![0, 1, 0], ![-9, 22, 9], ![-14, -23, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![56, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![56, 1, 0]] 
 ![![151, 0, 0], ![56, 1, 0], ![73, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![56, 1, 0], ![1, 53, 9], ![-79, -23, 60]]]
  hmulB := by decide  
  f := ![![![-1476, -99050, -16821], ![-1057, 282219, 0]], ![![-581, -36727, -6237], ![-301, 104643, 0]], ![![-708, -47885, -8132], ![-526, 136437, 0]]]
  g := ![![![1, 0, 0], ![-56, 151, 0], ![-73, 0, 151]], ![![0, 1, 0], ![-24, 53, 9], ![-21, -23, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![69, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![69, 1, 0]] 
 ![![151, 0, 0], ![69, 1, 0], ![31, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![69, 1, 0], ![1, 66, 9], ![-79, -23, 73]]]
  hmulB := by decide  
  f := ![![![-11371, -1133004, -154512], ![-12684, 2592368, 0]], ![![-5222, -517666, -70596], ![-5737, 1184444, 0]], ![![-2371, -232604, -31721], ![-2524, 532208, 0]]]
  g := ![![![1, 0, 0], ![-69, 151, 0], ![-31, 0, 151]], ![![0, 1, 0], ![-32, 66, 9], ![-5, -23, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![25, 1, 0]] ![![151, 0, 0], ![56, 1, 0]]
  ![![151, 0, 0], ![55, 59, 1]] where
 M := ![![![22801, 0, 0], ![8456, 151, 0]], ![![3775, 151, 0], ![1401, 78, 9]]]
 hmul := by decide  
 g := ![![![![96, -59, -1], ![151, 0, 0]], ![![1, -58, -1], ![151, 0, 0]]], ![![![-30, -58, -1], ![151, 0, 0]], ![![6, -3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![55, 59, 1]] ![![151, 0, 0], ![69, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![10419, 151, 0]], ![![8305, 8909, 151], ![3775, 3926, 604]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![69, 1, 0]]], ![![![55, 59, 1]], ![![25, 26, 4]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![82, 51, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![82, 51, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![82, 51, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![82, 51, 1], ![-28, -94, 463], ![-4093, -1192, 266]]]
  hmulB := by decide  
  f := ![![![-81, -51, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -51, 157]], ![![0, 0, 1], ![-242, -151, 463], ![-165, -94, 266]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [59, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 156], [0, 1]]
 g := ![![[130, 105], [144], [13, 93], [91, 106], [53, 147], [58], [1]], ![[33, 52], [144], [111, 64], [17, 51], [137, 10], [58], [1]]]
 h' := ![![[23, 156], [149, 133], [18, 12], [126, 90], [13, 109], [59, 33], [98, 23], [0, 1]], ![[0, 1], [68, 24], [137, 145], [155, 67], [8, 48], [33, 124], [156, 134], [23, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [126, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [59, 134, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6493250, -2045611, -5824264]
  a := ![-65, 132, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3000614, 1878929, -5824264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![8, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![8, 1, 0]] 
 ![![157, 0, 0], ![8, 1, 0], ![48, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![8, 1, 0], ![1, 5, 9], ![-79, -23, 12]]]
  hmulB := by decide  
  f := ![![![-1887, -9440, -16992], ![0, 296416, 0]], ![![-96, -480, -864], ![1, 15072, 0]], ![![-576, -2886, -5195], ![-18, 90624, 0]]]
  g := ![![![1, 0, 0], ![-8, 157, 0], ![-48, 0, 157]], ![![0, 1, 0], ![-3, 5, 9], ![-3, -23, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![82, 51, 1]] ![![157, 0, 0], ![8, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![1256, 157, 0]], ![![12874, 8007, 157], ![628, 314, 471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![8, 1, 0]]], ![![![82, 51, 1]], ![![4, 2, 3]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [62, 14, 159, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 146, 76], [2, 16, 87], [0, 1]]
 g := ![![[21, 96, 158], [118, 154, 61], [108, 132], [94, 65], [73, 38], [2, 4, 1], []], ![[84, 103, 68, 108], [17, 122, 93, 44], [18, 51], [132, 9], [97, 47], [72, 19, 25, 59], [145, 71]], ![[157, 122, 80, 121], [8, 64, 62, 58], [88, 34], [51, 133], [105, 24], [40, 36, 52, 41], [134, 71]]]
 h' := ![![[2, 146, 76], [19, 27, 141], [119, 153, 86], [28, 74, 28], [92, 33, 37], [39, 50, 53], [0, 0, 1], [0, 1]], ![[2, 16, 87], [46, 79, 70], [86, 97, 127], [77, 117, 41], [33, 16, 3], [4, 47, 84], [142, 20, 16], [2, 146, 76]], ![[0, 1], [38, 57, 115], [58, 76, 113], [102, 135, 94], [2, 114, 123], [127, 66, 26], [9, 143, 146], [2, 16, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 40], []]
 b := ![[], [48, 115, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [62, 14, 159, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4529281, -1421686, -4447618]
  a := ![-2, 8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27787, -8722, -27286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![74, -42, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![74, -42, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![74, 125, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![74, -42, 1], ![-121, 177, -374], ![3254, 947, -114]]]
  hmulB := by decide  
  f := ![![![-73, 42, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -125, 167]], ![![0, -1, 1], ![165, 281, -374], ![70, 91, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [50, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 166], [0, 1]]
 g := ![![[88, 157], [81, 154], [14, 6], [12], [28], [66, 24], [1]], ![[0, 10], [0, 13], [0, 161], [12], [28], [10, 143], [1]]]
 h' := ![![[109, 166], [125, 149], [135, 34], [155, 138], [33, 43], [40, 144], [117, 109], [0, 1]], ![[0, 1], [0, 18], [0, 133], [0, 29], [44, 124], [38, 23], [141, 58], [109, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [25, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [50, 58, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2343, -611, -2232]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![975, 1667, -2232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![40, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![40, 1, 0]] 
 ![![167, 0, 0], ![40, 1, 0], ![114, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![40, 1, 0], ![1, 37, 9], ![-79, -23, 44]]]
  hmulB := by decide  
  f := ![![![-7222, -296831, -72207], ![-3340, 1339841, 0]], ![![-1721, -71072, -17289], ![-834, 320807, 0]], ![![-4924, -202627, -49291], ![-2305, 914622, 0]]]
  g := ![![![1, 0, 0], ![-40, 167, 0], ![-114, 0, 167]], ![![0, 1, 0], ![-15, 37, 9], ![-25, -23, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![74, -42, 1]] ![![167, 0, 0], ![40, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![6680, 167, 0]], ![![12358, -7014, 167], ![2839, -1503, -334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![40, 1, 0]]], ![![![74, -42, 1]], ![![17, -9, -2]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![1, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![1, 1, 0]] 
 ![![173, 0, 0], ![1, 1, 0], ![58, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![1, 1, 0], ![1, -2, 9], ![-79, -23, 5]]]
  hmulB := by decide  
  f := ![![![-58, 115, -522], ![173, 10034, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-20, 38, -175], ![154, 3364, 0]]]
  g := ![![![1, 0, 0], ![-1, 173, 0], ![-58, 0, 173]], ![![0, 1, 0], ![-3, -2, 9], ![-2, -23, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![17, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![17, 1, 0]] 
 ![![173, 0, 0], ![17, 1, 0], ![89, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![17, 1, 0], ![1, 14, 9], ![-79, -23, 21]]]
  hmulB := by decide  
  f := ![![![-15743, -224208, -144144], ![-2768, 2770768, 0]], ![![-1556, -22021, -14157], ![-172, 272129, 0]], ![![-8099, -115344, -74155], ![-1424, 1425424, 0]]]
  g := ![![![1, 0, 0], ![-17, 173, 0], ![-89, 0, 173]], ![![0, 1, 0], ![-6, 14, 9], ![-9, -23, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-19, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-19, 1, 0]] 
 ![![173, 0, 0], ![154, 1, 0], ![69, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-19, 1, 0], ![1, -22, 9], ![-79, -23, -15]]]
  hmulB := by decide  
  f := ![![![-4325, 98091, -40131], ![1211, 771407, 0]], ![![-3854, 87312, -35721], ![1039, 686637, 0]], ![![-1725, 39123, -16006], ![483, 307671, 0]]]
  g := ![![![1, 0, 0], ![-154, 173, 0], ![-69, 0, 173]], ![![-1, 1, 0], ![16, -22, 9], ![26, -23, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![1, 1, 0]] ![![173, 0, 0], ![17, 1, 0]]
  ![![173, 0, 0], ![2, -56, 1]] where
 M := ![![![29929, 0, 0], ![2941, 173, 0]], ![![173, 173, 0], ![18, 15, 9]]]
 hmul := by decide  
 g := ![![![![171, 56, -1], ![173, 0, 0]], ![![17, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 3, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![2, -56, 1]] ![![173, 0, 0], ![-19, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-3287, 173, 0]], ![![346, -9688, 173], ![-173, 1211, -519]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-19, 1, 0]]], ![![![2, -56, 1]], ![![-1, 7, -3]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [87, 72, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 104, 143], [113, 74, 36], [0, 1]]
 g := ![![[100, 33, 67], [14, 163, 64], [154, 52], [169, 49], [116, 104, 82], [132, 5, 1], []], ![[62, 60, 62, 123], [14, 151, 146, 164], [152, 139], [45, 171], [114, 97, 142, 26], [119, 174, 61, 122], [66, 43]], ![[18, 92, 14, 110], [23, 79, 1, 117], [87, 68], [97, 5], [57, 74, 81, 110], [50, 133, 93, 51], [173, 43]]]
 h' := ![![[71, 104, 143], [35, 107, 109], [9, 158, 8], [124, 117, 125], [111, 31, 172], [151, 85, 34], [0, 0, 1], [0, 1]], ![[113, 74, 36], [138, 46, 97], [70, 44, 95], [103, 172, 26], [59, 111, 156], [73, 51, 172], [15, 10, 74], [71, 104, 143]], ![[0, 1], [26, 26, 152], [144, 156, 76], [175, 69, 28], [77, 37, 30], [9, 43, 152], [45, 169, 104], [113, 74, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 172], []]
 b := ![[], [84, 162, 144], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [87, 72, 174, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17200826, 4898335, -4020698]
  a := ![2, 14, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96094, 27365, -22462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -1, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![23, -1, 1]] 
 ![![181, 0, 0], ![73, 1, 0], ![96, 0, 1]] where
  M :=![![![23, -1, 1], ![-80, 3, -5], ![15, 4, -1]]]
  hmulB := by decide  
  f := ![![![17, 3, 2]], ![![6, 1, 1]], ![![7, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 3, -5], ![-1, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-66, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-66, 1, 0]] 
 ![![181, 0, 0], ![115, 1, 0], ![17, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-66, 1, 0], ![1, -69, 9], ![-79, -23, -62]]]
  hmulB := by decide  
  f := ![![![-4308, 392934, -51255], ![3801, 1030795, 0]], ![![-2693, 249628, -32562], ![2535, 654858, 0]], ![![-378, 36905, -4814], ![430, 96815, 0]]]
  g := ![![![1, 0, 0], ![-115, 181, 0], ![-17, 0, 181]], ![![-1, 1, 0], ![43, -69, 9], ![20, -23, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-8, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-8, 1, 0]] 
 ![![181, 0, 0], ![173, 1, 0], ![111, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-8, 1, 0], ![1, -11, 9], ![-79, -23, -4]]]
  hmulB := by decide  
  f := ![![![-14278, 157852, -129159], ![1629, 2597531, 0]], ![![-13651, 150868, -123444], ![1449, 2482596, 0]], ![![-8754, 96804, -79208], ![1047, 1592961, 0]]]
  g := ![![![1, 0, 0], ![-173, 181, 0], ![-111, 0, 181]], ![![-1, 1, 0], ![5, -11, 9], ![24, -23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![23, -1, 1]] ![![181, 0, 0], ![-66, 1, 0]]
  ![![181, 0, 0], ![48, -80, 1]] where
 M := ![![![4163, -181, 181], ![-1598, 69, -71]]]
 hmul := by decide  
 g := ![![![![-25, 79, 0], ![181, 0, 0]], ![![-38, 49, -1], ![110, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![48, -80, 1]] ![![181, 0, 0], ![-8, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-1448, 181, 0]], ![![8688, -14480, 181], ![-543, 905, -724]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-8, 1, 0]]], ![![![48, -80, 1]], ![![-3, 5, -4]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-76, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-76, 1, 0]] 
 ![![191, 0, 0], ![115, 1, 0], ![97, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-76, 1, 0], ![1, -79, 9], ![-79, -23, -72]]]
  hmulB := by decide  
  f := ![![![-10595, 1161246, -132300], ![10314, 2807700, 0]], ![![-6341, 699117, -79650], ![6304, 1690350, 0]], ![![-5325, 589742, -67189], ![5378, 1425900, 0]]]
  g := ![![![1, 0, 0], ![-115, 191, 0], ![-97, 0, 191]], ![![-1, 1, 0], ![43, -79, 9], ![50, -23, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-70, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-70, 1, 0]] 
 ![![191, 0, 0], ![121, 1, 0], ![69, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-70, 1, 0], ![1, -73, 9], ![-79, -23, -66]]]
  hmulB := by decide  
  f := ![![![-2289, 223369, -27540], ![2101, 584460, 0]], ![![-1447, 141467, -17442], ![1338, 370158, 0]], ![![-791, 80693, -9949], ![857, 211140, 0]]]
  g := ![![![1, 0, 0], ![-121, 191, 0], ![-69, 0, 191]], ![![-1, 1, 0], ![43, -73, 9], ![38, -23, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-46, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-46, 1, 0]] 
 ![![191, 0, 0], ![145, 1, 0], ![68, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-46, 1, 0], ![1, -49, 9], ![-79, -23, -42]]]
  hmulB := by decide  
  f := ![![![-4607, 255081, -46854], ![2483, 994346, 0]], ![![-3491, 193638, -35568], ![1911, 754832, 0]], ![![-1632, 90814, -16681], ![918, 354008, 0]]]
  g := ![![![1, 0, 0], ![-145, 191, 0], ![-68, 0, 191]], ![![-1, 1, 0], ![34, -49, 9], ![32, -23, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-76, 1, 0]] ![![191, 0, 0], ![-70, 1, 0]]
  ![![191, 0, 0], ![-3, -59, 1]] where
 M := ![![![36481, 0, 0], ![-13370, 191, 0]], ![![-14516, 191, 0], ![5321, -149, 9]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![-67, 60, -1], ![191, 0, 0]]], ![![![-73, 60, -1], ![191, 0, 0]], ![![28, 2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-3, -59, 1]] ![![191, 0, 0], ![-46, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-8786, 191, 0]], ![![-573, -11269, 191], ![0, 2865, -573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-46, 1, 0]]], ![![![-3, -59, 1]], ![![0, 15, -3]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-29, 61, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-29, 61, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![164, 61, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-29, 61, 1], ![-18, -235, 553], ![-4883, -1422, 195]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-164, -61, 193]], ![![-1, 0, 1], ![-470, -176, 553], ![-191, -69, 195]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [112, 181, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 192], [0, 1]]
 g := ![![[186, 81], [6], [18], [138], [4], [59], [12, 1]], ![[0, 112], [6], [18], [138], [4], [59], [24, 192]]]
 h' := ![![[12, 192], [108, 184], [89, 44], [91, 156], [140, 36], [3, 191], [7, 32], [0, 1]], ![[0, 1], [0, 9], [38, 149], [33, 37], [186, 157], [172, 2], [5, 161], [12, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [99, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [112, 181, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2810, 1989, -9301]
  a := ![-2, 8, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7918, 2950, -9301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![26, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![26, 1, 0]] 
 ![![193, 0, 0], ![26, 1, 0], ![191, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![26, 1, 0], ![1, 23, 9], ![-79, -23, 30]]]
  hmulB := by decide  
  f := ![![![-1013, -23919, -9360], ![-193, 200720, 0]], ![![-140, -3220, -1260], ![1, 27020, 0]], ![![-999, -23671, -9263], ![-217, 198640, 0]]]
  g := ![![![1, 0, 0], ![-26, 193, 0], ![-191, 0, 193]], ![![0, 1, 0], ![-12, 23, 9], ![-27, -23, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-29, 61, 1]] ![![193, 0, 0], ![26, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![5018, 193, 0]], ![![-5597, 11773, 193], ![-772, 1351, 579]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![26, 1, 0]]], ![![![-29, 61, 1]], ![![-4, 7, 3]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB212I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB212I3 : PrimesBelowBoundCertificateInterval O 137 193 212 where
  m := 11
  g := ![2, 2, 3, 2, 1, 2, 3, 1, 3, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB212I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
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
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![173, 173, 173]
    · exact ![5735339]
    · exact ![181, 181, 181]
    · exact ![191, 191, 191]
    · exact ![37249, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
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
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I167N1, I173N0, I173N1, I173N2, I181N0, I181N1, I181N2, I191N0, I191N1, I191N2, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [], [I167N1], [I173N0, I173N1, I173N2], [], [I181N0, I181N1, I181N2], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
